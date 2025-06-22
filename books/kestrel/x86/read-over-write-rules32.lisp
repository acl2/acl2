; "Read over write" rules for our x86 state readers and writers
;
; Copyright (C) 2016-2019 Kestrel Technology, LLC
; Copyright (C) 2020-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

(include-book "support32") ; reduce?  but we need at least the memory readers
(include-book "register-readers-and-writers32")

(defthm eax-of-write-byte-to-segment (equal (eax (write-byte-to-segment eff-addr seg-reg val x86)) (eax x86)) :hints (("Goal" :in-theory (enable write-byte-to-segment))))
(defthm ebx-of-write-byte-to-segment (equal (ebx (write-byte-to-segment eff-addr seg-reg val x86)) (ebx x86)) :hints (("Goal" :in-theory (enable write-byte-to-segment))))
(defthm ecx-of-write-byte-to-segment (equal (ecx (write-byte-to-segment eff-addr seg-reg val x86)) (ecx x86)) :hints (("Goal" :in-theory (enable write-byte-to-segment))))
(defthm edx-of-write-byte-to-segment (equal (edx (write-byte-to-segment eff-addr seg-reg val x86)) (edx x86)) :hints (("Goal" :in-theory (enable write-byte-to-segment))))
(defthm esp-of-write-byte-to-segment (equal (esp (write-byte-to-segment eff-addr seg-reg val x86)) (esp x86)) :hints (("Goal" :in-theory (enable write-byte-to-segment))))
(defthm ebp-of-write-byte-to-segment (equal (ebp (write-byte-to-segment eff-addr seg-reg val x86)) (ebp x86)) :hints (("Goal" :in-theory (enable write-byte-to-segment))))

(defthm eax-of-write-to-segment (equal (eax (write-to-segment n eff-addr seg-reg val x86)) (eax x86)) :hints (("Goal" :in-theory (enable write-to-segment))))
(defthm ebx-of-write-to-segment (equal (ebx (write-to-segment n eff-addr seg-reg val x86)) (ebx x86)) :hints (("Goal" :in-theory (enable write-to-segment))))
(defthm ecx-of-write-to-segment (equal (ecx (write-to-segment n eff-addr seg-reg val x86)) (ecx x86)) :hints (("Goal" :in-theory (enable write-to-segment))))
(defthm edx-of-write-to-segment (equal (edx (write-to-segment n eff-addr seg-reg val x86)) (edx x86)) :hints (("Goal" :in-theory (enable write-to-segment))))
(defthm esp-of-write-to-segment (equal (esp (write-to-segment n eff-addr seg-reg val x86)) (esp x86)) :hints (("Goal" :in-theory (enable write-to-segment))))
(defthm ebp-of-write-to-segment (equal (ebp (write-to-segment n eff-addr seg-reg val x86)) (ebp x86)) :hints (("Goal" :in-theory (enable write-to-segment))))

(defthm rax-high-of-write-byte-to-segment (equal (rax-high (write-byte-to-segment eff-addr seg-reg val x86)) (rax-high x86)) :hints (("Goal" :in-theory (enable write-byte-to-segment))))
(defthm rbx-high-of-write-byte-to-segment (equal (rbx-high (write-byte-to-segment eff-addr seg-reg val x86)) (rbx-high x86)) :hints (("Goal" :in-theory (enable write-byte-to-segment))))
(defthm rcx-high-of-write-byte-to-segment (equal (rcx-high (write-byte-to-segment eff-addr seg-reg val x86)) (rcx-high x86)) :hints (("Goal" :in-theory (enable write-byte-to-segment))))
(defthm rdx-high-of-write-byte-to-segment (equal (rdx-high (write-byte-to-segment eff-addr seg-reg val x86)) (rdx-high x86)) :hints (("Goal" :in-theory (enable write-byte-to-segment))))
(defthm rsp-high-of-write-byte-to-segment (equal (rsp-high (write-byte-to-segment eff-addr seg-reg val x86)) (rsp-high x86)) :hints (("Goal" :in-theory (enable write-byte-to-segment))))
(defthm rbp-high-of-write-byte-to-segment (equal (rbp-high (write-byte-to-segment eff-addr seg-reg val x86)) (rbp-high x86)) :hints (("Goal" :in-theory (enable write-byte-to-segment))))

(defthm rax-high-of-write-to-segment (equal (rax-high (write-to-segment n eff-addr seg-reg val x86)) (rax-high x86)) :hints (("Goal" :in-theory (enable write-to-segment))))
(defthm rbx-high-of-write-to-segment (equal (rbx-high (write-to-segment n eff-addr seg-reg val x86)) (rbx-high x86)) :hints (("Goal" :in-theory (enable write-to-segment))))
(defthm rcx-high-of-write-to-segment (equal (rcx-high (write-to-segment n eff-addr seg-reg val x86)) (rcx-high x86)) :hints (("Goal" :in-theory (enable write-to-segment))))
(defthm rdx-high-of-write-to-segment (equal (rdx-high (write-to-segment n eff-addr seg-reg val x86)) (rdx-high x86)) :hints (("Goal" :in-theory (enable write-to-segment))))
(defthm rsp-high-of-write-to-segment (equal (rsp-high (write-to-segment n eff-addr seg-reg val x86)) (rsp-high x86)) :hints (("Goal" :in-theory (enable write-to-segment))))
(defthm rbp-high-of-write-to-segment (equal (rbp-high (write-to-segment n eff-addr seg-reg val x86)) (rbp-high x86)) :hints (("Goal" :in-theory (enable write-to-segment))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm read-byte-from-segment-of-set-eip (equal (read-byte-from-segment eff-addr seg-reg (set-eip eip x86)) (read-byte-from-segment eff-addr seg-reg x86)) :hints (("Goal" :in-theory (enable set-eip))))
(defthm read-byte-from-segment-of-set-eax (equal (read-byte-from-segment eff-addr seg-reg (set-eax val x86)) (read-byte-from-segment eff-addr seg-reg x86)) :hints (("Goal" :in-theory (enable set-eax))))
(defthm read-byte-from-segment-of-set-ebx (equal (read-byte-from-segment eff-addr seg-reg (set-ebx val x86)) (read-byte-from-segment eff-addr seg-reg x86)) :hints (("Goal" :in-theory (enable set-ebx))))
(defthm read-byte-from-segment-of-set-ecx (equal (read-byte-from-segment eff-addr seg-reg (set-ecx val x86)) (read-byte-from-segment eff-addr seg-reg x86)) :hints (("Goal" :in-theory (enable set-ecx))))
(defthm read-byte-from-segment-of-set-edx (equal (read-byte-from-segment eff-addr seg-reg (set-edx val x86)) (read-byte-from-segment eff-addr seg-reg x86)) :hints (("Goal" :in-theory (enable set-edx))))
(defthm read-byte-from-segment-of-set-esp (equal (read-byte-from-segment eff-addr seg-reg (set-esp val x86)) (read-byte-from-segment eff-addr seg-reg x86)) :hints (("Goal" :in-theory (enable set-esp))))
(defthm read-byte-from-segment-of-set-ebp (equal (read-byte-from-segment eff-addr seg-reg (set-ebp val x86)) (read-byte-from-segment eff-addr seg-reg x86)) :hints (("Goal" :in-theory (enable set-ebp))))

;(defthm read-byte-from-segment-of-set-rip-high (equal (read-byte-from-segment eff-addr seg-reg (set-rip-high val x86)) (read-byte-from-segment eff-addr seg-reg x86)) :hints (("Goal" :in-theory (enable set-rip-high))))
(defthm read-byte-from-segment-of-set-rax-high (equal (read-byte-from-segment eff-addr seg-reg (set-rax-high val x86)) (read-byte-from-segment eff-addr seg-reg x86)) :hints (("Goal" :in-theory (enable set-rax-high))))
(defthm read-byte-from-segment-of-set-rbx-high (equal (read-byte-from-segment eff-addr seg-reg (set-rbx-high val x86)) (read-byte-from-segment eff-addr seg-reg x86)) :hints (("Goal" :in-theory (enable set-rbx-high))))
(defthm read-byte-from-segment-of-set-rcx-high (equal (read-byte-from-segment eff-addr seg-reg (set-rcx-high val x86)) (read-byte-from-segment eff-addr seg-reg x86)) :hints (("Goal" :in-theory (enable set-rcx-high))))
(defthm read-byte-from-segment-of-set-rdx-high (equal (read-byte-from-segment eff-addr seg-reg (set-rdx-high val x86)) (read-byte-from-segment eff-addr seg-reg x86)) :hints (("Goal" :in-theory (enable set-rdx-high))))
(defthm read-byte-from-segment-of-set-rsp-high (equal (read-byte-from-segment eff-addr seg-reg (set-rsp-high val x86)) (read-byte-from-segment eff-addr seg-reg x86)) :hints (("Goal" :in-theory (enable set-rsp-high))))
(defthm read-byte-from-segment-of-set-rbp-high (equal (read-byte-from-segment eff-addr seg-reg (set-rbp-high val x86)) (read-byte-from-segment eff-addr seg-reg x86)) :hints (("Goal" :in-theory (enable set-rbp-high))))

(defthm read-byte-from-segment-of-set-mxcsr
  (equal (read-byte-from-segment eff-addr seg-reg (set-mxcsr mxcsr x86))
         (read-byte-from-segment eff-addr seg-reg x86))
  :hints (("Goal" :in-theory (enable set-mxcsr))))

(defthm read-byte-from-segment-of-set-flag
  (equal (read-byte-from-segment eff-addr seg-reg (set-flag flg val x86))
         (read-byte-from-segment eff-addr seg-reg x86))
  :hints (("Goal" :in-theory (enable set-flag))))

(defthm read-byte-from-segment-of-set-undef
  (equal (read-byte-from-segment eff-addr seg-reg (set-undef undef x86))
         (read-byte-from-segment eff-addr seg-reg x86))
  :hints (("Goal" :in-theory (enable set-undef))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm read-byte-list-from-segment-of-set-flag
  (equal (read-byte-list-from-segment n eff-addr seg-reg (set-flag flg val x86))
         (read-byte-list-from-segment n eff-addr seg-reg x86))
  :hints (("Goal" :in-theory (enable read-byte-list-from-segment))))

(defthm read-byte-list-from-segment-of-set-mxcsr
  (equal (read-byte-list-from-segment n eff-addr seg-reg (set-mxcsr mxcsr x86))
         (read-byte-list-from-segment n eff-addr seg-reg x86))
  :hints (("Goal" :in-theory (enable read-byte-list-from-segment))))

(defthm read-byte-list-from-segment-of-set-undef
  (equal (read-byte-list-from-segment n eff-addr seg-reg (set-undef undef x86))
         (read-byte-list-from-segment n eff-addr seg-reg x86))
  :hints (("Goal" :in-theory (enable read-byte-list-from-segment))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm read-from-segment-of-set-eip (equal (read-from-segment n eff-addr seg-reg (set-eip eip x86)) (read-from-segment n eff-addr seg-reg x86)) :hints (("Goal" :in-theory (enable set-eip))))
(defthm read-from-segment-of-set-eax (equal (read-from-segment n eff-addr seg-reg (set-eax val x86)) (read-from-segment n eff-addr seg-reg x86)) :hints (("Goal" :in-theory (enable set-eax))))
(defthm read-from-segment-of-set-ebx (equal (read-from-segment n eff-addr seg-reg (set-ebx val x86)) (read-from-segment n eff-addr seg-reg x86)) :hints (("Goal" :in-theory (enable set-ebx))))
(defthm read-from-segment-of-set-ecx (equal (read-from-segment n eff-addr seg-reg (set-ecx val x86)) (read-from-segment n eff-addr seg-reg x86)) :hints (("Goal" :in-theory (enable set-ecx))))
(defthm read-from-segment-of-set-edx (equal (read-from-segment n eff-addr seg-reg (set-edx val x86)) (read-from-segment n eff-addr seg-reg x86)) :hints (("Goal" :in-theory (enable set-edx))))
(defthm read-from-segment-of-set-esp (equal (read-from-segment n eff-addr seg-reg (set-esp val x86)) (read-from-segment n eff-addr seg-reg x86)) :hints (("Goal" :in-theory (enable set-esp))))
(defthm read-from-segment-of-set-ebp (equal (read-from-segment n eff-addr seg-reg (set-ebp val x86)) (read-from-segment n eff-addr seg-reg x86)) :hints (("Goal" :in-theory (enable set-ebp))))

(defthm read-from-segment-of-set-rax-high (equal (read-from-segment n eff-addr seg-reg (set-rax-high val x86)) (read-from-segment n eff-addr seg-reg x86)) :hints (("Goal" :in-theory (enable set-rax-high))))
(defthm read-from-segment-of-set-rbx-high (equal (read-from-segment n eff-addr seg-reg (set-rbx-high val x86)) (read-from-segment n eff-addr seg-reg x86)) :hints (("Goal" :in-theory (enable set-rbx-high))))
(defthm read-from-segment-of-set-rcx-high (equal (read-from-segment n eff-addr seg-reg (set-rcx-high val x86)) (read-from-segment n eff-addr seg-reg x86)) :hints (("Goal" :in-theory (enable set-rcx-high))))
(defthm read-from-segment-of-set-rdx-high (equal (read-from-segment n eff-addr seg-reg (set-rdx-high val x86)) (read-from-segment n eff-addr seg-reg x86)) :hints (("Goal" :in-theory (enable set-rdx-high))))
(defthm read-from-segment-of-set-rsp-high (equal (read-from-segment n eff-addr seg-reg (set-rsp-high val x86)) (read-from-segment n eff-addr seg-reg x86)) :hints (("Goal" :in-theory (enable set-rsp-high))))
(defthm read-from-segment-of-set-rbp-high (equal (read-from-segment n eff-addr seg-reg (set-rbp-high val x86)) (read-from-segment n eff-addr seg-reg x86)) :hints (("Goal" :in-theory (enable set-rbp-high))))

(defthm read-from-segment-of-set-flag
  (equal (read-from-segment n eff-addr seg-reg (set-flag flg val x86))
         (read-from-segment n eff-addr seg-reg x86))
  :hints (("Goal" :in-theory (enable read-from-segment))))

(defthm read-from-segment-of-set-undef
  (equal (read-from-segment n eff-addr seg-reg (set-undef undef x86))
         (read-from-segment n eff-addr seg-reg x86))
  :hints (("Goal" :in-theory (enable read-from-segment))))

(defthm read-from-segment-of-set-mxcsr
  (equal (read-from-segment n eff-addr seg-reg (set-mxcsr mxcsr x86))
         (read-from-segment n eff-addr seg-reg x86))
  :hints (("Goal" :in-theory (enable read-from-segment))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm segment-is-32-bitsp-of-set-eip
  (equal (segment-is-32-bitsp seg-reg (set-eip eip x86))
         (segment-is-32-bitsp seg-reg x86))
  :hints (("Goal" :in-theory (enable set-eip))))

(defthm segment-is-32-bitsp-of-set-eax (equal (segment-is-32-bitsp seg-reg (set-eax eax x86)) (segment-is-32-bitsp seg-reg x86)) :hints (("Goal" :in-theory (enable set-eax))))
(defthm segment-is-32-bitsp-of-set-ebx (equal (segment-is-32-bitsp seg-reg (set-ebx ebx x86)) (segment-is-32-bitsp seg-reg x86)) :hints (("Goal" :in-theory (enable set-ebx))))
(defthm segment-is-32-bitsp-of-set-ecx (equal (segment-is-32-bitsp seg-reg (set-ecx ecx x86)) (segment-is-32-bitsp seg-reg x86)) :hints (("Goal" :in-theory (enable set-ecx))))
(defthm segment-is-32-bitsp-of-set-edx (equal (segment-is-32-bitsp seg-reg (set-edx edx x86)) (segment-is-32-bitsp seg-reg x86)) :hints (("Goal" :in-theory (enable set-edx))))
(defthm segment-is-32-bitsp-of-set-esp (equal (segment-is-32-bitsp seg-reg (set-esp esp x86)) (segment-is-32-bitsp seg-reg x86)) :hints (("Goal" :in-theory (enable set-esp))))
(defthm segment-is-32-bitsp-of-set-ebp (equal (segment-is-32-bitsp seg-reg (set-ebp ebp x86)) (segment-is-32-bitsp seg-reg x86)) :hints (("Goal" :in-theory (enable set-ebp))))

(defthm segment-is-32-bitsp-of-set-rax-high (equal (segment-is-32-bitsp seg-reg (set-rax-high eax x86)) (segment-is-32-bitsp seg-reg x86)) :hints (("Goal" :in-theory (enable set-rax-high))))
(defthm segment-is-32-bitsp-of-set-rbx-high (equal (segment-is-32-bitsp seg-reg (set-rbx-high ebx x86)) (segment-is-32-bitsp seg-reg x86)) :hints (("Goal" :in-theory (enable set-rbx-high))))
(defthm segment-is-32-bitsp-of-set-rcx-high (equal (segment-is-32-bitsp seg-reg (set-rcx-high ecx x86)) (segment-is-32-bitsp seg-reg x86)) :hints (("Goal" :in-theory (enable set-rcx-high))))
(defthm segment-is-32-bitsp-of-set-rdx-high (equal (segment-is-32-bitsp seg-reg (set-rdx-high edx x86)) (segment-is-32-bitsp seg-reg x86)) :hints (("Goal" :in-theory (enable set-rdx-high))))
(defthm segment-is-32-bitsp-of-set-rsp-high (equal (segment-is-32-bitsp seg-reg (set-rsp-high esp x86)) (segment-is-32-bitsp seg-reg x86)) :hints (("Goal" :in-theory (enable set-rsp-high))))
(defthm segment-is-32-bitsp-of-set-rbp-high (equal (segment-is-32-bitsp seg-reg (set-rbp-high ebp x86)) (segment-is-32-bitsp seg-reg x86)) :hints (("Goal" :in-theory (enable set-rbp-high))))

(defthm segment-is-32-bitsp-of-write-byte-to-segment
  (equal (segment-is-32-bitsp seg-reg1 (write-byte-to-segment eff-addr seg-reg2 val x86))
         (segment-is-32-bitsp seg-reg1 x86))
  :hints (("Goal" :in-theory (enable write-byte-to-segment))))

(defthm segment-is-32-bitsp-of-write-to-segment
  (equal (segment-is-32-bitsp seg-reg1 (write-to-segment n eff-addr seg-reg2 val x86))
         (segment-is-32-bitsp seg-reg1 x86))
  :hints (("Goal" :in-theory (enable write-to-segment))))

(defthm segment-is-32-bitsp-of-set-flag
  (equal (segment-is-32-bitsp seg-reg (set-flag flg val x86))
         (segment-is-32-bitsp seg-reg x86))
  :hints (("Goal" :in-theory (enable segment-is-32-bitsp))))

(defthm segment-is-32-bitsp-of-set-undef
  (equal (segment-is-32-bitsp seg-reg (set-undef undef x86))
         (segment-is-32-bitsp seg-reg x86))
  :hints (("Goal" :in-theory (enable segment-is-32-bitsp))))

(defthm segment-is-32-bitsp-of-set-mxcsr
  (equal (segment-is-32-bitsp seg-reg (set-mxcsr mxcsr x86))
         (segment-is-32-bitsp seg-reg x86))
  :hints (("Goal" :in-theory (enable segment-is-32-bitsp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm 32-bit-segment-start-and-size-of-write-to-segment
  (equal (32-bit-segment-start-and-size seg-reg (write-to-segment n eff-addr seg-reg2 val x86))
         (32-bit-segment-start-and-size seg-reg x86))
  :hints (("Goal" :in-theory (enable 32-bit-segment-start-and-size))))

(defthm 32-bit-segment-start-and-size-of-set-flag
  (equal (32-bit-segment-start-and-size seg-reg (set-flag flg val x86))
         (32-bit-segment-start-and-size seg-reg x86))
  :hints (("Goal" :in-theory (enable 32-bit-segment-start-and-size))))

(defthm 32-bit-segment-start-and-size-of-set-undef
  (equal (32-bit-segment-start-and-size seg-reg (set-undef undef x86))
         (32-bit-segment-start-and-size seg-reg x86))
  :hints (("Goal" :in-theory (enable 32-bit-segment-start-and-size))))

(defthm 32-bit-segment-start-and-size-of-set-mxcsr
  (equal (32-bit-segment-start-and-size seg-reg (set-mxcsr mxcsr x86))
         (32-bit-segment-start-and-size seg-reg x86))
  :hints (("Goal" :in-theory (enable 32-bit-segment-start-and-size))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm 32-bit-segment-start-of-set-eip
  (equal (32-bit-segment-start seg-reg (set-eip eip x86))
         (32-bit-segment-start seg-reg x86))
  :hints (("Goal" :in-theory (enable set-eip 32-bit-segment-size 32-bit-segment-start 32-bit-segment-start-and-size))))

(defthm 32-bit-segment-start-of-set-eax (equal (32-bit-segment-start seg-reg (set-eax eax x86)) (32-bit-segment-start seg-reg x86)) :hints (("Goal" :in-theory (enable set-eax))))
(defthm 32-bit-segment-start-of-set-ebx (equal (32-bit-segment-start seg-reg (set-ebx ebx x86)) (32-bit-segment-start seg-reg x86)) :hints (("Goal" :in-theory (enable set-ebx))))
(defthm 32-bit-segment-start-of-set-ecx (equal (32-bit-segment-start seg-reg (set-ecx ecx x86)) (32-bit-segment-start seg-reg x86)) :hints (("Goal" :in-theory (enable set-ecx))))
(defthm 32-bit-segment-start-of-set-edx (equal (32-bit-segment-start seg-reg (set-edx edx x86)) (32-bit-segment-start seg-reg x86)) :hints (("Goal" :in-theory (enable set-edx))))
(defthm 32-bit-segment-start-of-set-esp (equal (32-bit-segment-start seg-reg (set-esp esp x86)) (32-bit-segment-start seg-reg x86)) :hints (("Goal" :in-theory (enable set-esp))))
(defthm 32-bit-segment-start-of-set-ebp (equal (32-bit-segment-start seg-reg (set-ebp ebp x86)) (32-bit-segment-start seg-reg x86)) :hints (("Goal" :in-theory (enable set-ebp))))

(defthm 32-bit-segment-start-of-set-rax-high (equal (32-bit-segment-start seg-reg (set-rax-high eax x86)) (32-bit-segment-start seg-reg x86)) :hints (("Goal" :in-theory (enable set-rax-high))))
(defthm 32-bit-segment-start-of-set-rbx-high (equal (32-bit-segment-start seg-reg (set-rbx-high ebx x86)) (32-bit-segment-start seg-reg x86)) :hints (("Goal" :in-theory (enable set-rbx-high))))
(defthm 32-bit-segment-start-of-set-rcx-high (equal (32-bit-segment-start seg-reg (set-rcx-high ecx x86)) (32-bit-segment-start seg-reg x86)) :hints (("Goal" :in-theory (enable set-rcx-high))))
(defthm 32-bit-segment-start-of-set-rdx-high (equal (32-bit-segment-start seg-reg (set-rdx-high edx x86)) (32-bit-segment-start seg-reg x86)) :hints (("Goal" :in-theory (enable set-rdx-high))))
(defthm 32-bit-segment-start-of-set-rsp-high (equal (32-bit-segment-start seg-reg (set-rsp-high esp x86)) (32-bit-segment-start seg-reg x86)) :hints (("Goal" :in-theory (enable set-rsp-high))))
(defthm 32-bit-segment-start-of-set-rbp-high (equal (32-bit-segment-start seg-reg (set-rbp-high ebp x86)) (32-bit-segment-start seg-reg x86)) :hints (("Goal" :in-theory (enable set-rbp-high))))

(defthm 32-bit-segment-start-of-write-byte-to-segment
  (equal (32-bit-segment-start seg-reg1 (write-byte-to-segment eff-addr seg-reg2 val x86))
         (32-bit-segment-start seg-reg1 x86))
  :hints (("Goal" :in-theory (enable write-byte-to-segment 32-bit-segment-start))))

(defthm 32-bit-segment-start-of-write-to-segment
  (equal (32-bit-segment-start seg-reg (write-to-segment n eff-addr seg-reg2 val x86))
         (32-bit-segment-start seg-reg x86))
  :hints (("Goal" :in-theory (enable 32-bit-segment-start))))

(defthm 32-bit-segment-start-of-set-flag
  (equal (32-bit-segment-start seg-reg (set-flag flg val x86))
         (32-bit-segment-start seg-reg x86))
  :hints (("Goal" :in-theory (enable 32-bit-segment-start))))

(defthm 32-bit-segment-start-of-set-mxcsr
  (equal (32-bit-segment-start seg-reg (set-mxcsr mxcsr x86))
         (32-bit-segment-start seg-reg x86))
  :hints (("Goal" :in-theory (enable 32-bit-segment-start))))

(defthm 32-bit-segment-start-of-set-undef
  (equal (32-bit-segment-start seg-reg (set-undef undef x86))
         (32-bit-segment-start seg-reg x86))
  :hints (("Goal" :in-theory (enable 32-bit-segment-start))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm segment-base-and-bounds-of-set-eip (equal (segment-base-and-bounds proc-mode seg-reg (set-eip eip x86)) (segment-base-and-bounds proc-mode seg-reg x86)) :hints (("Goal" :in-theory (enable set-eip))))
(defthm segment-base-and-bounds-of-set-eax (equal (segment-base-and-bounds proc-mode seg-reg (set-eax eax x86)) (segment-base-and-bounds proc-mode seg-reg x86)) :hints (("Goal" :in-theory (enable set-eax))))
(defthm segment-base-and-bounds-of-set-ebx (equal (segment-base-and-bounds proc-mode seg-reg (set-ebx ebx x86)) (segment-base-and-bounds proc-mode seg-reg x86)) :hints (("Goal" :in-theory (enable set-ebx))))
(defthm segment-base-and-bounds-of-set-ecx (equal (segment-base-and-bounds proc-mode seg-reg (set-ecx ecx x86)) (segment-base-and-bounds proc-mode seg-reg x86)) :hints (("Goal" :in-theory (enable set-ecx))))
(defthm segment-base-and-bounds-of-set-edx (equal (segment-base-and-bounds proc-mode seg-reg (set-edx edx x86)) (segment-base-and-bounds proc-mode seg-reg x86)) :hints (("Goal" :in-theory (enable set-edx))))
(defthm segment-base-and-bounds-of-set-esp (equal (segment-base-and-bounds proc-mode seg-reg (set-esp esp x86)) (segment-base-and-bounds proc-mode seg-reg x86)) :hints (("Goal" :in-theory (enable set-esp))))
(defthm segment-base-and-bounds-of-set-ebp (equal (segment-base-and-bounds proc-mode seg-reg (set-ebp ebp x86)) (segment-base-and-bounds proc-mode seg-reg x86)) :hints (("Goal" :in-theory (enable set-ebp))))

(defthm segment-base-and-bounds-of-set-rax-high (equal (segment-base-and-bounds proc-mode seg-reg (set-rax-high eax x86)) (segment-base-and-bounds proc-mode seg-reg x86)) :hints (("Goal" :in-theory (enable set-rax-high))))
(defthm segment-base-and-bounds-of-set-rbx-high (equal (segment-base-and-bounds proc-mode seg-reg (set-rbx-high ebx x86)) (segment-base-and-bounds proc-mode seg-reg x86)) :hints (("Goal" :in-theory (enable set-rbx-high))))
(defthm segment-base-and-bounds-of-set-rcx-high (equal (segment-base-and-bounds proc-mode seg-reg (set-rcx-high ecx x86)) (segment-base-and-bounds proc-mode seg-reg x86)) :hints (("Goal" :in-theory (enable set-rcx-high))))
(defthm segment-base-and-bounds-of-set-rdx-high (equal (segment-base-and-bounds proc-mode seg-reg (set-rdx-high edx x86)) (segment-base-and-bounds proc-mode seg-reg x86)) :hints (("Goal" :in-theory (enable set-rdx-high))))
(defthm segment-base-and-bounds-of-set-rsp-high (equal (segment-base-and-bounds proc-mode seg-reg (set-rsp-high esp x86)) (segment-base-and-bounds proc-mode seg-reg x86)) :hints (("Goal" :in-theory (enable set-rsp-high))))
(defthm segment-base-and-bounds-of-set-rbp-high (equal (segment-base-and-bounds proc-mode seg-reg (set-rbp-high ebp x86)) (segment-base-and-bounds proc-mode seg-reg x86)) :hints (("Goal" :in-theory (enable set-rbp-high))))

(defthm segment-base-and-bounds-of-write-byte-to-segment
  (equal (segment-base-and-bounds proc-mode seg-reg (write-byte-to-segment eff-addr seg-reg2 val x86))
         (segment-base-and-bounds proc-mode seg-reg x86))
  :hints (("Goal" :in-theory (enable write-byte-to-segment))))

(defthm segment-base-and-bounds-of-write-to-segment
  (equal (segment-base-and-bounds proc-mode seg-reg (write-to-segment n eff-addr seg-reg2 val x86))
         (segment-base-and-bounds proc-mode seg-reg x86))
  :hints (("Goal" :in-theory (enable write-to-segment))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Are these used?

(defthm segment-min-eff-addr32-of-set-eip
  (equal (segment-min-eff-addr32 seg-reg (set-eip eip x86))
         (segment-min-eff-addr32 seg-reg x86))
  :hints (("Goal" :in-theory (enable segment-min-eff-addr32))))

(defthm segment-min-eff-addr32-of-set-flag
  (equal (segment-min-eff-addr32 seg-reg (set-flag flg val x86))
         (segment-min-eff-addr32 seg-reg x86))
  :hints (("Goal" :in-theory (enable set-flag))))

(defthm segment-min-eff-addr32-of-write-byte-to-segment
  (equal (segment-min-eff-addr32 seg-reg (write-byte-to-segment eff-addr2 seg-reg2 val x86))
         (segment-min-eff-addr32 seg-reg x86))
  :hints (("Goal" :in-theory (enable segment-min-eff-addr32))))

(defthm segment-min-eff-addr32-of-write-to-segment
  (equal (segment-min-eff-addr32 seg-reg (write-to-segment n eff-addr seg-reg2 val x86))
         (segment-min-eff-addr32 seg-reg x86))
  :hints (("Goal" :in-theory (enable segment-min-eff-addr32))))

(defthm segment-min-eff-addr32-of-set-undef (equal (segment-min-eff-addr32 seg-reg (set-undef undef x86)) (segment-min-eff-addr32 seg-reg x86)) :hints (("Goal" :in-theory (enable set-undef))))
(defthm segment-min-eff-addr32-of-set-mxcsr (equal (segment-min-eff-addr32 seg-reg (set-mxcsr mxcsr x86)) (segment-min-eff-addr32 seg-reg x86)) :hints (("Goal" :in-theory (enable set-mxcsr))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Are these used?

(defthm segment-max-eff-addr32-of-set-eip
  (equal (segment-max-eff-addr32 seg-reg (set-eip eip x86))
         (segment-max-eff-addr32 seg-reg x86))
  :hints (("Goal" :in-theory (enable segment-max-eff-addr32))))

(defthm segment-max-eff-addr32-of-set-flag
  (equal (segment-max-eff-addr32 seg-reg (set-flag flg val x86))
         (segment-max-eff-addr32 seg-reg x86))
  :hints (("Goal" :in-theory (enable set-flag))))

(defthm segment-max-eff-addr32-of-write-byte-to-segment
  (equal (segment-max-eff-addr32 seg-reg (write-byte-to-segment eff-addr2 seg-reg2 val x86))
         (segment-max-eff-addr32 seg-reg x86))
  :hints (("Goal" :in-theory (enable segment-max-eff-addr32))))

(defthm segment-max-eff-addr32-of-write-to-segment
  (equal (segment-max-eff-addr32 seg-reg (write-to-segment n eff-addr seg-reg2 val x86))
         (segment-max-eff-addr32 seg-reg x86))
  :hints (("Goal" :in-theory (enable segment-max-eff-addr32))))

(defthm segment-max-eff-addr32-of-set-undef
  (equal (segment-max-eff-addr32 seg-reg (set-undef undef x86))
         (segment-max-eff-addr32 seg-reg x86))
  :hints (("Goal" :in-theory (enable set-undef))))

(defthm segment-max-eff-addr32-of-set-mxcsr
  (equal (segment-max-eff-addr32 seg-reg (set-mxcsr mxcsr x86))
         (segment-max-eff-addr32 seg-reg x86))
  :hints (("Goal" :in-theory (enable set-mxcsr))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm 32-bit-segment-size-of-set-eip (equal (32-bit-segment-size seg-reg (set-eip eip x86)) (32-bit-segment-size seg-reg x86)) :hints (("Goal" :in-theory (enable set-eip))))

(defthm 32-bit-segment-size-of-set-eax (equal (32-bit-segment-size seg-reg (set-eax eax x86)) (32-bit-segment-size seg-reg x86)) :hints (("Goal" :in-theory (enable set-eax))))
(defthm 32-bit-segment-size-of-set-ebx (equal (32-bit-segment-size seg-reg (set-ebx ebx x86)) (32-bit-segment-size seg-reg x86)) :hints (("Goal" :in-theory (enable set-ebx))))
(defthm 32-bit-segment-size-of-set-ecx (equal (32-bit-segment-size seg-reg (set-ecx ecx x86)) (32-bit-segment-size seg-reg x86)) :hints (("Goal" :in-theory (enable set-ecx))))
(defthm 32-bit-segment-size-of-set-edx (equal (32-bit-segment-size seg-reg (set-edx edx x86)) (32-bit-segment-size seg-reg x86)) :hints (("Goal" :in-theory (enable set-edx))))
(defthm 32-bit-segment-size-of-set-esp (equal (32-bit-segment-size seg-reg (set-esp esp x86)) (32-bit-segment-size seg-reg x86)) :hints (("Goal" :in-theory (enable set-esp))))
(defthm 32-bit-segment-size-of-set-ebp (equal (32-bit-segment-size seg-reg (set-ebp ebp x86)) (32-bit-segment-size seg-reg x86)) :hints (("Goal" :in-theory (enable set-ebp))))

(defthm 32-bit-segment-size-of-set-rax-high (equal (32-bit-segment-size seg-reg (set-rax-high eax x86)) (32-bit-segment-size seg-reg x86)) :hints (("Goal" :in-theory (enable set-rax-high))))
(defthm 32-bit-segment-size-of-set-rbx-high (equal (32-bit-segment-size seg-reg (set-rbx-high ebx x86)) (32-bit-segment-size seg-reg x86)) :hints (("Goal" :in-theory (enable set-rbx-high))))
(defthm 32-bit-segment-size-of-set-rcx-high (equal (32-bit-segment-size seg-reg (set-rcx-high ecx x86)) (32-bit-segment-size seg-reg x86)) :hints (("Goal" :in-theory (enable set-rcx-high))))
(defthm 32-bit-segment-size-of-set-rdx-high (equal (32-bit-segment-size seg-reg (set-rdx-high edx x86)) (32-bit-segment-size seg-reg x86)) :hints (("Goal" :in-theory (enable set-rdx-high))))
(defthm 32-bit-segment-size-of-set-rsp-high (equal (32-bit-segment-size seg-reg (set-rsp-high esp x86)) (32-bit-segment-size seg-reg x86)) :hints (("Goal" :in-theory (enable set-rsp-high))))
(defthm 32-bit-segment-size-of-set-rbp-high (equal (32-bit-segment-size seg-reg (set-rbp-high ebp x86)) (32-bit-segment-size seg-reg x86)) :hints (("Goal" :in-theory (enable set-rbp-high))))

(defthm 32-bit-segment-size-of-write-byte-to-segment (equal (32-bit-segment-size seg-reg1 (write-byte-to-segment eff-addr seg-reg2 val x86)) (32-bit-segment-size seg-reg1 x86)) :hints (("Goal" :in-theory (enable write-byte-to-segment))))
(defthm 32-bit-segment-size-of-write-to-segment (equal (32-bit-segment-size seg-reg1 (write-to-segment n eff-addr seg-reg2 val x86)) (32-bit-segment-size seg-reg1 x86)) :hints (("Goal" :in-theory (enable 32-bit-segment-size))))

(defthm 32-bit-segment-size-of-set-flag
  (equal (32-bit-segment-size seg-reg (set-flag flg val x86))
         (32-bit-segment-size seg-reg x86))
  :hints (("Goal" :in-theory (enable 32-bit-segment-size))))

(defthm 32-bit-segment-size-of-set-undef
  (equal (32-bit-segment-size seg-reg (set-undef undef x86))
         (32-bit-segment-size seg-reg x86))
  :hints (("Goal" :in-theory (enable 32-bit-segment-size))))

(defthm 32-bit-segment-size-of-set-mxcsr
  (equal (32-bit-segment-size seg-reg (set-mxcsr mxcsr x86))
         (32-bit-segment-size seg-reg x86))
  :hints (("Goal" :in-theory (enable 32-bit-segment-size))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm segment-expand-down-bit-of-set-eip (equal (segment-expand-down-bit seg-reg (set-eip eip x86)) (segment-expand-down-bit seg-reg x86)) :hints (("Goal" :in-theory (enable set-eip))))

(defthm segment-expand-down-bit-of-set-eax (equal (segment-expand-down-bit seg-reg (set-eax eax x86)) (segment-expand-down-bit seg-reg x86)) :hints (("Goal" :in-theory (enable set-eax))))
(defthm segment-expand-down-bit-of-set-ebx (equal (segment-expand-down-bit seg-reg (set-ebx ebx x86)) (segment-expand-down-bit seg-reg x86)) :hints (("Goal" :in-theory (enable set-ebx))))
(defthm segment-expand-down-bit-of-set-ecx (equal (segment-expand-down-bit seg-reg (set-ecx ecx x86)) (segment-expand-down-bit seg-reg x86)) :hints (("Goal" :in-theory (enable set-ecx))))
(defthm segment-expand-down-bit-of-set-edx (equal (segment-expand-down-bit seg-reg (set-edx edx x86)) (segment-expand-down-bit seg-reg x86)) :hints (("Goal" :in-theory (enable set-edx))))
(defthm segment-expand-down-bit-of-set-esp (equal (segment-expand-down-bit seg-reg (set-esp esp x86)) (segment-expand-down-bit seg-reg x86)) :hints (("Goal" :in-theory (enable set-esp))))
(defthm segment-expand-down-bit-of-set-ebp (equal (segment-expand-down-bit seg-reg (set-ebp ebp x86)) (segment-expand-down-bit seg-reg x86)) :hints (("Goal" :in-theory (enable set-ebp))))

(defthm segment-expand-down-bit-of-set-rax-high (equal (segment-expand-down-bit seg-reg (set-rax-high eax x86)) (segment-expand-down-bit seg-reg x86)) :hints (("Goal" :in-theory (enable set-rax-high))))
(defthm segment-expand-down-bit-of-set-rbx-high (equal (segment-expand-down-bit seg-reg (set-rbx-high ebx x86)) (segment-expand-down-bit seg-reg x86)) :hints (("Goal" :in-theory (enable set-rbx-high))))
(defthm segment-expand-down-bit-of-set-rcx-high (equal (segment-expand-down-bit seg-reg (set-rcx-high ecx x86)) (segment-expand-down-bit seg-reg x86)) :hints (("Goal" :in-theory (enable set-rcx-high))))
(defthm segment-expand-down-bit-of-set-rdx-high (equal (segment-expand-down-bit seg-reg (set-rdx-high edx x86)) (segment-expand-down-bit seg-reg x86)) :hints (("Goal" :in-theory (enable set-rdx-high))))
(defthm segment-expand-down-bit-of-set-rsp-high (equal (segment-expand-down-bit seg-reg (set-rsp-high esp x86)) (segment-expand-down-bit seg-reg x86)) :hints (("Goal" :in-theory (enable set-rsp-high))))
(defthm segment-expand-down-bit-of-set-rbp-high (equal (segment-expand-down-bit seg-reg (set-rbp-high ebp x86)) (segment-expand-down-bit seg-reg x86)) :hints (("Goal" :in-theory (enable set-rbp-high))))

(defthm segment-expand-down-bit-of-set-flag
  (equal (segment-expand-down-bit seg-reg (set-flag flg val x86))
         (segment-expand-down-bit seg-reg x86))
  :hints (("Goal" :in-theory (enable set-flag))))

(defthm segment-expand-down-bit-of-set-undef (equal (segment-expand-down-bit seg-reg (set-undef undef x86)) (segment-expand-down-bit seg-reg x86)) :hints (("Goal" :in-theory (enable set-undef))))
(defthm segment-expand-down-bit-of-set-mxcsr (equal (segment-expand-down-bit seg-reg (set-mxcsr mxcsr x86)) (segment-expand-down-bit seg-reg x86)) :hints (("Goal" :in-theory (enable set-mxcsr))))

(defthm segment-expand-down-bit-of-write-byte-to-segment
  (equal (segment-expand-down-bit seg-reg1 (write-byte-to-segment eff-addr seg-reg2 val x86))
         (segment-expand-down-bit seg-reg1 x86))
  :hints (("Goal" :in-theory (enable write-byte-to-segment 32-bit-segment-size 32-bit-segment-start-and-size))))

(defthm segment-expand-down-bit-of-write-to-segment
  (equal (segment-expand-down-bit seg-reg1 (write-to-segment n eff-addr seg-reg2 val x86))
         (segment-expand-down-bit seg-reg1 x86))
  :hints (("Goal" :in-theory (e/d (segment-expand-down-bit) (segment-expand-down-bit-intro)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm well-formed-32-bit-segmentp-of-set-eip
  (equal (well-formed-32-bit-segmentp seg-reg (set-eip eip x86))
         (well-formed-32-bit-segmentp seg-reg x86))
  :hints (("Goal" :in-theory (enable set-eip))))

(defthm well-formed-32-bit-segmentp-of-set-eax (equal (well-formed-32-bit-segmentp seg-reg (set-eax eax x86)) (well-formed-32-bit-segmentp seg-reg x86)) :hints (("Goal" :in-theory (enable set-eax))))
(defthm well-formed-32-bit-segmentp-of-set-ebx (equal (well-formed-32-bit-segmentp seg-reg (set-ebx ebx x86)) (well-formed-32-bit-segmentp seg-reg x86)) :hints (("Goal" :in-theory (enable set-ebx))))
(defthm well-formed-32-bit-segmentp-of-set-ecx (equal (well-formed-32-bit-segmentp seg-reg (set-ecx ecx x86))(well-formed-32-bit-segmentp seg-reg x86)) :hints (("Goal" :in-theory (enable set-ecx))))
(defthm well-formed-32-bit-segmentp-of-set-edx (equal (well-formed-32-bit-segmentp seg-reg (set-edx edx x86)) (well-formed-32-bit-segmentp seg-reg x86)) :hints (("Goal" :in-theory (enable set-edx))))
(defthm well-formed-32-bit-segmentp-of-set-esp (equal (well-formed-32-bit-segmentp seg-reg (set-esp esp x86)) (well-formed-32-bit-segmentp seg-reg x86)) :hints (("Goal" :in-theory (enable set-esp))))
(defthm well-formed-32-bit-segmentp-of-set-ebp (equal (well-formed-32-bit-segmentp seg-reg (set-ebp ebp x86)) (well-formed-32-bit-segmentp seg-reg x86)) :hints (("Goal" :in-theory (enable set-ebp))))

(defthm well-formed-32-bit-segmentp-of-set-rax-high (equal (well-formed-32-bit-segmentp seg-reg (set-rax-high eax x86)) (well-formed-32-bit-segmentp seg-reg x86)) :hints (("Goal" :in-theory (enable set-rax-high))))
(defthm well-formed-32-bit-segmentp-of-set-rbx-high (equal (well-formed-32-bit-segmentp seg-reg (set-rbx-high ebx x86)) (well-formed-32-bit-segmentp seg-reg x86)) :hints (("Goal" :in-theory (enable set-rbx-high))))
(defthm well-formed-32-bit-segmentp-of-set-rcx-high (equal (well-formed-32-bit-segmentp seg-reg (set-rcx-high ecx x86))(well-formed-32-bit-segmentp seg-reg x86)) :hints (("Goal" :in-theory (enable set-rcx-high))))
(defthm well-formed-32-bit-segmentp-of-set-rdx-high (equal (well-formed-32-bit-segmentp seg-reg (set-rdx-high edx x86)) (well-formed-32-bit-segmentp seg-reg x86)) :hints (("Goal" :in-theory (enable set-rdx-high))))
(defthm well-formed-32-bit-segmentp-of-set-rsp-high (equal (well-formed-32-bit-segmentp seg-reg (set-rsp-high esp x86)) (well-formed-32-bit-segmentp seg-reg x86)) :hints (("Goal" :in-theory (enable set-rsp-high))))
(defthm well-formed-32-bit-segmentp-of-set-rbp-high (equal (well-formed-32-bit-segmentp seg-reg (set-rbp-high ebp x86)) (well-formed-32-bit-segmentp seg-reg x86)) :hints (("Goal" :in-theory (enable set-rbp-high))))

(defthm well-formed-32-bit-segmentp-of-write-byte-to-segment
  (equal (well-formed-32-bit-segmentp seg-reg1 (write-byte-to-segment eff-addr seg-reg2 val x86))
         (well-formed-32-bit-segmentp seg-reg1 x86))
  :hints (("Goal" :in-theory (enable write-byte-to-segment))))

(defthm well-formed-32-bit-segmentp-of-write-to-segment
  (equal (well-formed-32-bit-segmentp seg-reg1 (write-to-segment n eff-addr seg-reg2 val x86))
         (well-formed-32-bit-segmentp seg-reg1 x86))
  :hints (("Goal" :in-theory (enable write-to-segment))))

(defthm well-formed-32-bit-segmentp-of-set-flag
  (equal (well-formed-32-bit-segmentp seg-reg (set-flag flg val x86))
         (well-formed-32-bit-segmentp seg-reg x86))
  :hints (("Goal" :in-theory (enable well-formed-32-bit-segmentp))))

(defthm well-formed-32-bit-segmentp-of-set-undef
  (equal (well-formed-32-bit-segmentp seg-reg (set-undef undef x86))
         (well-formed-32-bit-segmentp seg-reg x86))
  :hints (("Goal" :in-theory (enable well-formed-32-bit-segmentp set-undef))))

(defthm well-formed-32-bit-segmentp-of-set-mxcsr
  (equal (well-formed-32-bit-segmentp seg-reg (set-mxcsr mxcsr x86))
         (well-formed-32-bit-segmentp seg-reg x86))
  :hints (("Goal" :in-theory (enable well-formed-32-bit-segmentp set-mxcsr))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm segments-separate-of-set-eip (equal (segments-separate seg-reg1 seg-reg2 (set-eip eip x86)) (segments-separate seg-reg1 seg-reg2 x86)) :hints (("Goal" :in-theory (enable set-eip))))

(defthm segments-separate-of-set-eax (equal (segments-separate seg-reg1 seg-reg2 (set-eax eax x86)) (segments-separate seg-reg1 seg-reg2 x86)) :hints (("Goal" :in-theory (enable set-eax))))
(defthm segments-separate-of-set-ebx (equal (segments-separate seg-reg1 seg-reg2 (set-ebx ebx x86)) (segments-separate seg-reg1 seg-reg2 x86)) :hints (("Goal" :in-theory (enable set-ebx))))
(defthm segments-separate-of-set-ecx (equal (segments-separate seg-reg1 seg-reg2 (set-ecx ecx x86)) (segments-separate seg-reg1 seg-reg2 x86)) :hints (("Goal" :in-theory (enable set-ecx))))
(defthm segments-separate-of-set-edx (equal (segments-separate seg-reg1 seg-reg2 (set-edx edx x86)) (segments-separate seg-reg1 seg-reg2 x86)) :hints (("Goal" :in-theory (enable set-edx))))
(defthm segments-separate-of-set-esp (equal (segments-separate seg-reg1 seg-reg2 (set-esp esp x86)) (segments-separate seg-reg1 seg-reg2 x86)) :hints (("Goal" :in-theory (enable set-esp))))
(defthm segments-separate-of-set-ebp (equal (segments-separate seg-reg1 seg-reg2 (set-ebp ebp x86)) (segments-separate seg-reg1 seg-reg2 x86)) :hints (("Goal" :in-theory (enable set-ebp))))

(defthm segments-separate-of-set-rax-high (equal (segments-separate seg-reg1 seg-reg2 (set-rax-high eax x86)) (segments-separate seg-reg1 seg-reg2 x86)) :hints (("Goal" :in-theory (enable set-rax-high))))
(defthm segments-separate-of-set-rbx-high (equal (segments-separate seg-reg1 seg-reg2 (set-rbx-high ebx x86)) (segments-separate seg-reg1 seg-reg2 x86)) :hints (("Goal" :in-theory (enable set-rbx-high))))
(defthm segments-separate-of-set-rcx-high (equal (segments-separate seg-reg1 seg-reg2 (set-rcx-high ecx x86)) (segments-separate seg-reg1 seg-reg2 x86)) :hints (("Goal" :in-theory (enable set-rcx-high))))
(defthm segments-separate-of-set-rdx-high (equal (segments-separate seg-reg1 seg-reg2 (set-rdx-high edx x86)) (segments-separate seg-reg1 seg-reg2 x86)) :hints (("Goal" :in-theory (enable set-rdx-high))))
(defthm segments-separate-of-set-rsp-high (equal (segments-separate seg-reg1 seg-reg2 (set-rsp-high esp x86)) (segments-separate seg-reg1 seg-reg2 x86)) :hints (("Goal" :in-theory (enable set-rsp-high))))
(defthm segments-separate-of-set-rbp-high (equal (segments-separate seg-reg1 seg-reg2 (set-rbp-high ebp x86)) (segments-separate seg-reg1 seg-reg2 x86)) :hints (("Goal" :in-theory (enable set-rbp-high))))

(defthm segments-separate-of-write-byte-to-segment
  (equal (segments-separate seg-reg1 seg-reg2 (write-byte-to-segment eff-addr seg-reg3 val x86))
         (segments-separate seg-reg1 seg-reg2 x86))
  :hints (("Goal" :in-theory (e/d (write-byte-to-segment
                                   segments-separate
                                   32-bit-segment-size
                                   32-bit-segment-start-and-size)
                                  (;; x86isa::seg-hidden-limiti-is-n32p
                                   ;; x86isa::seg-hidden-basei-is-n64p
                                   )))))

(defthm segments-separate-of-write-to-segment
  (equal (segments-separate seg-reg1 seg-reg2 (write-to-segment n eff-addr seg-reg val x86))
         (segments-separate seg-reg1 seg-reg2 x86))
  :hints (("Goal" :in-theory (enable segments-separate))))

(defthm segments-separate-of-set-flag
  (equal (segments-separate seg-reg1 seg-reg2 (set-flag flag val x86))
         (segments-separate seg-reg1 seg-reg2 x86))
  :hints (("Goal" :in-theory (enable set-flag segments-separate segments-separate-helper))))

(defthm segments-separate-of-set-undef
  (equal (segments-separate seg-reg1 seg-reg2 (set-undef undef x86))
         (segments-separate seg-reg1 seg-reg2 x86))
  :hints (("Goal" :in-theory (enable set-undef segments-separate segments-separate-helper))))

(defthm segments-separate-of-set-mxcsr
  (equal (segments-separate seg-reg1 seg-reg2 (set-mxcsr mxcsr x86))
         (segments-separate seg-reg1 seg-reg2 x86))
  :hints (("Goal" :in-theory (enable set-mxcsr segments-separate segments-separate-helper))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm code-and-stack-segments-separate-of-set-eax (equal (code-and-stack-segments-separate (set-eax eax x86)) (code-and-stack-segments-separate x86)) :hints (("Goal" :in-theory (enable set-eax))))
(defthm code-and-stack-segments-separate-of-set-ebx (equal (code-and-stack-segments-separate (set-ebx ebx x86)) (code-and-stack-segments-separate x86)) :hints (("Goal" :in-theory (enable set-ebx))))
(defthm code-and-stack-segments-separate-of-set-ecx (equal (code-and-stack-segments-separate (set-ecx ecx x86)) (code-and-stack-segments-separate x86)) :hints (("Goal" :in-theory (enable set-ecx))))
(defthm code-and-stack-segments-separate-of-set-edx (equal (code-and-stack-segments-separate (set-edx edx x86)) (code-and-stack-segments-separate x86)) :hints (("Goal" :in-theory (enable set-edx))))
(defthm code-and-stack-segments-separate-of-set-esp (equal (code-and-stack-segments-separate (set-esp esp x86)) (code-and-stack-segments-separate x86)) :hints (("Goal" :in-theory (enable set-esp))))
(defthm code-and-stack-segments-separate-of-set-ebp (equal (code-and-stack-segments-separate (set-ebp ebp x86)) (code-and-stack-segments-separate x86)) :hints (("Goal" :in-theory (enable set-ebp))))

(defthm code-and-stack-segments-separate-of-set-rax-high (equal (code-and-stack-segments-separate (set-rax-high eax x86)) (code-and-stack-segments-separate x86)) :hints (("Goal" :in-theory (enable set-rax-high))))
(defthm code-and-stack-segments-separate-of-set-rbx-high (equal (code-and-stack-segments-separate (set-rbx-high ebx x86)) (code-and-stack-segments-separate x86)) :hints (("Goal" :in-theory (enable set-rbx-high))))
(defthm code-and-stack-segments-separate-of-set-rcx-high (equal (code-and-stack-segments-separate (set-rcx-high ecx x86)) (code-and-stack-segments-separate x86)) :hints (("Goal" :in-theory (enable set-rcx-high))))
(defthm code-and-stack-segments-separate-of-set-rdx-high (equal (code-and-stack-segments-separate (set-rdx-high edx x86)) (code-and-stack-segments-separate x86)) :hints (("Goal" :in-theory (enable set-rdx-high))))
(defthm code-and-stack-segments-separate-of-set-rsp-high (equal (code-and-stack-segments-separate (set-rsp-high esp x86)) (code-and-stack-segments-separate x86)) :hints (("Goal" :in-theory (enable set-rsp-high))))
(defthm code-and-stack-segments-separate-of-set-rbp-high (equal (code-and-stack-segments-separate (set-rbp-high ebp x86)) (code-and-stack-segments-separate x86)) :hints (("Goal" :in-theory (enable set-rbp-high))))

(defthm code-and-stack-segments-separate-of-set-eip
  (equal (code-and-stack-segments-separate (set-eip eip x86))
         (code-and-stack-segments-separate x86))
  :hints (("Goal" :in-theory (enable code-and-stack-segments-separate))))

(defthm code-and-stack-segments-separate-of-set-flag
  (equal (code-and-stack-segments-separate (set-flag flag val x86))
         (code-and-stack-segments-separate x86))
  :hints (("Goal" :in-theory (enable code-and-stack-segments-separate))))

(defthm code-and-stack-segments-separate-of-set-undef
  (equal (code-and-stack-segments-separate (set-undef undef x86))
         (code-and-stack-segments-separate x86))
  :hints (("Goal" :in-theory (enable code-and-stack-segments-separate))))

(defthm code-and-stack-segments-separate-of-set-mxcsr
  (equal (code-and-stack-segments-separate (set-mxcsr mxcsr x86))
         (code-and-stack-segments-separate x86))
  :hints (("Goal" :in-theory (enable code-and-stack-segments-separate))))

(defthm code-and-stack-segments-separate-of-write-byte-to-segment
  (equal (code-and-stack-segments-separate (write-byte-to-segment eff-addr seg-reg val x86))
         (code-and-stack-segments-separate x86))
  :hints (("Goal" :in-theory (enable code-and-stack-segments-separate))))

(defthm code-and-stack-segments-separate-of-write-to-segment
  (equal (code-and-stack-segments-separate (write-to-segment n eff-addr seg-reg val x86))
         (code-and-stack-segments-separate x86))
  :hints (("Goal" :in-theory (enable code-and-stack-segments-separate))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm alignment-checking-enabled-p-of-set-eip
  (equal (alignment-checking-enabled-p (set-eip eip x86))
         (alignment-checking-enabled-p x86))
  :hints (("Goal" :in-theory (enable set-eip))))

(defthm alignment-checking-enabled-p-of-set-eax (equal (alignment-checking-enabled-p (set-eax eax x86)) (alignment-checking-enabled-p x86)) :hints (("Goal" :in-theory (enable set-eax))))
(defthm alignment-checking-enabled-p-of-set-ebx (equal (alignment-checking-enabled-p (set-ebx ebx x86)) (alignment-checking-enabled-p x86)) :hints (("Goal" :in-theory (enable set-ebx))))
(defthm alignment-checking-enabled-p-of-set-ecx (equal (alignment-checking-enabled-p (set-ecx ecx x86)) (alignment-checking-enabled-p x86)) :hints (("Goal" :in-theory (enable set-ecx))))
(defthm alignment-checking-enabled-p-of-set-edx (equal (alignment-checking-enabled-p (set-edx edx x86)) (alignment-checking-enabled-p x86)) :hints (("Goal" :in-theory (enable set-edx))))
(defthm alignment-checking-enabled-p-of-set-esp (equal (alignment-checking-enabled-p (set-esp esp x86)) (alignment-checking-enabled-p x86)) :hints (("Goal" :in-theory (enable set-esp))))
(defthm alignment-checking-enabled-p-of-set-ebp (equal (alignment-checking-enabled-p (set-ebp ebp x86)) (alignment-checking-enabled-p x86)) :hints (("Goal" :in-theory (enable set-ebp))))

(defthm alignment-checking-enabled-p-of-set-rax-high (equal (alignment-checking-enabled-p (set-rax-high eax x86)) (alignment-checking-enabled-p x86)) :hints (("Goal" :in-theory (enable set-rax-high))))
(defthm alignment-checking-enabled-p-of-set-rbx-high (equal (alignment-checking-enabled-p (set-rbx-high ebx x86)) (alignment-checking-enabled-p x86)) :hints (("Goal" :in-theory (enable set-rbx-high))))
(defthm alignment-checking-enabled-p-of-set-rcx-high (equal (alignment-checking-enabled-p (set-rcx-high ecx x86)) (alignment-checking-enabled-p x86)) :hints (("Goal" :in-theory (enable set-rcx-high))))
(defthm alignment-checking-enabled-p-of-set-rdx-high (equal (alignment-checking-enabled-p (set-rdx-high edx x86)) (alignment-checking-enabled-p x86)) :hints (("Goal" :in-theory (enable set-rdx-high))))
(defthm alignment-checking-enabled-p-of-set-rsp-high (equal (alignment-checking-enabled-p (set-rsp-high esp x86)) (alignment-checking-enabled-p x86)) :hints (("Goal" :in-theory (enable set-rsp-high))))
(defthm alignment-checking-enabled-p-of-set-rbp-high (equal (alignment-checking-enabled-p (set-rbp-high ebp x86)) (alignment-checking-enabled-p x86)) :hints (("Goal" :in-theory (enable set-rbp-high))))

(defthm alignment-checking-enabled-p-of-write-byte-to-segment
  (equal (alignment-checking-enabled-p (write-byte-to-segment eff-addr seg-reg val x86))
         (alignment-checking-enabled-p x86))
  :hints (("Goal" :in-theory (enable write-byte-to-segment))))

(defthm alignment-checking-enabled-p-of-write-to-segment
  (equal (alignment-checking-enabled-p (write-to-segment n eff-addr seg-reg val x86))
         (alignment-checking-enabled-p x86))
  :hints (("Goal" :in-theory (enable write-to-segment))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm get-flag-of-set-eip (equal (get-flag flag (set-eip eip x86)) (get-flag flag x86)) :hints (("Goal" :in-theory (enable set-eip))))

(defthm get-flag-of-set-eax (equal (get-flag flag (set-eax eax x86)) (get-flag flag x86)) :hints (("Goal" :in-theory (enable set-eax))))
(defthm get-flag-of-set-ebx (equal (get-flag flag (set-ebx ebx x86)) (get-flag flag x86)) :hints (("Goal" :in-theory (enable set-ebx))))
(defthm get-flag-of-set-ecx (equal (get-flag flag (set-ecx ecx x86)) (get-flag flag x86)) :hints (("Goal" :in-theory (enable set-ecx))))
(defthm get-flag-of-set-edx (equal (get-flag flag (set-edx edx x86)) (get-flag flag x86)) :hints (("Goal" :in-theory (enable set-edx))))
(defthm get-flag-of-set-esp (equal (get-flag flag (set-esp esp x86)) (get-flag flag x86)) :hints (("Goal" :in-theory (enable set-esp))))
(defthm get-flag-of-set-ebp (equal (get-flag flag (set-ebp ebp x86)) (get-flag flag x86)) :hints (("Goal" :in-theory (enable set-ebp))))

(defthm get-flag-of-set-rax-high (equal (get-flag flag (set-rax-high eax x86)) (get-flag flag x86)) :hints (("Goal" :in-theory (enable set-rax-high))))
(defthm get-flag-of-set-rbx-high (equal (get-flag flag (set-rbx-high ebx x86)) (get-flag flag x86)) :hints (("Goal" :in-theory (enable set-rbx-high))))
(defthm get-flag-of-set-rcx-high (equal (get-flag flag (set-rcx-high ecx x86)) (get-flag flag x86)) :hints (("Goal" :in-theory (enable set-rcx-high))))
(defthm get-flag-of-set-rdx-high (equal (get-flag flag (set-rdx-high edx x86)) (get-flag flag x86)) :hints (("Goal" :in-theory (enable set-rdx-high))))
(defthm get-flag-of-set-rsp-high (equal (get-flag flag (set-rsp-high esp x86)) (get-flag flag x86)) :hints (("Goal" :in-theory (enable set-rsp-high))))
(defthm get-flag-of-set-rbp-high (equal (get-flag flag (set-rbp-high ebp x86)) (get-flag flag x86)) :hints (("Goal" :in-theory (enable set-rbp-high))))

(defthm get-flag-of-write-byte-to-segment
  (equal (get-flag flag (write-byte-to-segment eff-addr seg-reg val x86))
         (get-flag flag x86))
  :hints (("Goal" :in-theory (enable write-byte-to-segment))))

(defthm get-flag-of-write-to-segment
  (equal (get-flag flag (write-to-segment n eff-addr seg-reg val x86))
         (get-flag flag x86))
  :hints (("Goal" :in-theory (enable write-to-segment))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; (defthm eff-addr-okp-of-set-reg-high
;;   (equal (eff-addr-okp eff-addr seg-reg (set-reg-high reg val x86))
;;          (eff-addr-okp eff-addr seg-reg x86))
;;   :hints (("Goal" :in-theory (enable set-reg-high))))

(defthm eff-addr-okp-of-set-eip (equal (eff-addr-okp eff-addr seg-reg (set-eip eip x86)) (eff-addr-okp eff-addr seg-reg x86)) :hints (("Goal" :in-theory (enable set-eip))))

(defthm eff-addr-okp-of-set-eax (equal (eff-addr-okp eff-addr seg-reg (set-eax eax x86)) (eff-addr-okp eff-addr seg-reg x86)) :hints (("Goal" :in-theory (enable set-eax))))
(defthm eff-addr-okp-of-set-ebx (equal (eff-addr-okp eff-addr seg-reg (set-ebx ebx x86)) (eff-addr-okp eff-addr seg-reg x86)) :hints (("Goal" :in-theory (enable set-ebx))))
(defthm eff-addr-okp-of-set-ecx (equal (eff-addr-okp eff-addr seg-reg (set-ecx ecx x86)) (eff-addr-okp eff-addr seg-reg x86)) :hints (("Goal" :in-theory (enable set-ecx))))
(defthm eff-addr-okp-of-set-edx (equal (eff-addr-okp eff-addr seg-reg (set-edx edx x86)) (eff-addr-okp eff-addr seg-reg x86)) :hints (("Goal" :in-theory (enable set-edx))))
(defthm eff-addr-okp-of-set-esp (equal (eff-addr-okp eff-addr seg-reg (set-esp esp x86)) (eff-addr-okp eff-addr seg-reg x86)) :hints (("Goal" :in-theory (enable set-esp))))
(defthm eff-addr-okp-of-set-ebp (equal (eff-addr-okp eff-addr seg-reg (set-ebp ebp x86)) (eff-addr-okp eff-addr seg-reg x86)) :hints (("Goal" :in-theory (enable set-ebp))))

(defthm eff-addr-okp-of-set-rax-high (equal (eff-addr-okp eff-addr seg-reg (set-rax-high eax x86)) (eff-addr-okp eff-addr seg-reg x86)) :hints (("Goal" :in-theory (enable set-rax-high))))
(defthm eff-addr-okp-of-set-rbx-high (equal (eff-addr-okp eff-addr seg-reg (set-rbx-high ebx x86)) (eff-addr-okp eff-addr seg-reg x86)) :hints (("Goal" :in-theory (enable set-rbx-high))))
(defthm eff-addr-okp-of-set-rcx-high (equal (eff-addr-okp eff-addr seg-reg (set-rcx-high ecx x86)) (eff-addr-okp eff-addr seg-reg x86)) :hints (("Goal" :in-theory (enable set-rcx-high))))
(defthm eff-addr-okp-of-set-rdx-high (equal (eff-addr-okp eff-addr seg-reg (set-rdx-high edx x86)) (eff-addr-okp eff-addr seg-reg x86)) :hints (("Goal" :in-theory (enable set-rdx-high))))
(defthm eff-addr-okp-of-set-rsp-high (equal (eff-addr-okp eff-addr seg-reg (set-rsp-high esp x86)) (eff-addr-okp eff-addr seg-reg x86)) :hints (("Goal" :in-theory (enable set-rsp-high))))
(defthm eff-addr-okp-of-set-rbp-high (equal (eff-addr-okp eff-addr seg-reg (set-rbp-high ebp x86)) (eff-addr-okp eff-addr seg-reg x86)) :hints (("Goal" :in-theory (enable set-rbp-high))))

(defthm eff-addr-okp-of-set-flag
  (equal (eff-addr-okp eff-addr seg-reg (set-flag flg val x86))
         (eff-addr-okp eff-addr seg-reg x86)))



(defthm eff-addr-okp-of-set-undef
  (equal (eff-addr-okp eff-addr seg-reg (set-undef undef x86))
         (eff-addr-okp eff-addr seg-reg x86))
  :hints (("Goal" :in-theory (enable set-undef))))

(defthm eff-addr-okp-of-set-mxcsr
  (equal (eff-addr-okp eff-addr seg-reg (set-mxcsr mxcsr x86))
         (eff-addr-okp eff-addr seg-reg x86))
  :hints (("Goal" :in-theory (enable set-mxcsr))))

(defthm eff-addr-okp-of-write-to-segment
  (equal (eff-addr-okp eff-addr seg-reg (write-to-segment n2 eff-addr2 seg-reg2 val2 x86))
         (eff-addr-okp eff-addr seg-reg x86)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm eff-addrs-okp-of-set-eip (equal (eff-addrs-okp n eff-addr seg-reg (set-eip eip x86)) (eff-addrs-okp n eff-addr seg-reg x86)) :hints (("Goal" :in-theory (enable set-eip))))

(defthm eff-addrs-okp-of-set-eax (equal (eff-addrs-okp n eff-addr seg-reg (set-eax eax x86)) (eff-addrs-okp n eff-addr seg-reg x86)) :hints (("Goal" :in-theory (enable set-eax))))
(defthm eff-addrs-okp-of-set-ebx (equal (eff-addrs-okp n eff-addr seg-reg (set-ebx ebx x86)) (eff-addrs-okp n eff-addr seg-reg x86)) :hints (("Goal" :in-theory (enable set-ebx))))
(defthm eff-addrs-okp-of-set-ecx (equal (eff-addrs-okp n eff-addr seg-reg (set-ecx ecx x86)) (eff-addrs-okp n eff-addr seg-reg x86)) :hints (("Goal" :in-theory (enable set-ecx))))
(defthm eff-addrs-okp-of-set-edx (equal (eff-addrs-okp n eff-addr seg-reg (set-edx edx x86)) (eff-addrs-okp n eff-addr seg-reg x86)) :hints (("Goal" :in-theory (enable set-edx))))
(defthm eff-addrs-okp-of-set-esp (equal (eff-addrs-okp n eff-addr seg-reg (set-esp esp x86)) (eff-addrs-okp n eff-addr seg-reg x86)) :hints (("Goal" :in-theory (enable set-esp))))
(defthm eff-addrs-okp-of-set-ebp (equal (eff-addrs-okp n eff-addr seg-reg (set-ebp ebp x86)) (eff-addrs-okp n eff-addr seg-reg x86)) :hints (("Goal" :in-theory (enable set-ebp))))

(defthm eff-addrs-okp-of-set-rax-high (equal (eff-addrs-okp n eff-addr seg-reg (set-rax-high eax x86)) (eff-addrs-okp n eff-addr seg-reg x86)) :hints (("Goal" :in-theory (enable set-rax-high))))
(defthm eff-addrs-okp-of-set-rbx-high (equal (eff-addrs-okp n eff-addr seg-reg (set-rbx-high ebx x86)) (eff-addrs-okp n eff-addr seg-reg x86)) :hints (("Goal" :in-theory (enable set-rbx-high))))
(defthm eff-addrs-okp-of-set-rcx-high (equal (eff-addrs-okp n eff-addr seg-reg (set-rcx-high ecx x86)) (eff-addrs-okp n eff-addr seg-reg x86)) :hints (("Goal" :in-theory (enable set-rcx-high))))
(defthm eff-addrs-okp-of-set-rdx-high (equal (eff-addrs-okp n eff-addr seg-reg (set-rdx-high edx x86)) (eff-addrs-okp n eff-addr seg-reg x86)) :hints (("Goal" :in-theory (enable set-rdx-high))))
(defthm eff-addrs-okp-of-set-rsp-high (equal (eff-addrs-okp n eff-addr seg-reg (set-rsp-high esp x86)) (eff-addrs-okp n eff-addr seg-reg x86)) :hints (("Goal" :in-theory (enable set-rsp-high))))
(defthm eff-addrs-okp-of-set-rbp-high (equal (eff-addrs-okp n eff-addr seg-reg (set-rbp-high ebp x86)) (eff-addrs-okp n eff-addr seg-reg x86)) :hints (("Goal" :in-theory (enable set-rbp-high))))

(defthm eff-addrs-okp-of-set-flag
  (equal (eff-addrs-okp n eff-addr seg-reg (set-flag flg val x86))
         (eff-addrs-okp n eff-addr seg-reg x86)))

(defthm eff-addrs-okp-of-set-undef
  (equal (eff-addrs-okp n eff-addr seg-reg (set-undef undef x86))
         (eff-addrs-okp n eff-addr seg-reg x86)))

(defthm eff-addrs-okp-of-set-mxcsr
  (equal (eff-addrs-okp n eff-addr seg-reg (set-mxcsr mxcsr x86))
         (eff-addrs-okp n eff-addr seg-reg x86)))

(defthm eff-addrs-okp-of-write-to-segment
  (equal (eff-addrs-okp n eff-addr seg-reg (write-to-segment n2 eff-addr2 seg-reg2 val2 x86))
         (eff-addrs-okp n eff-addr seg-reg x86)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm 64-bit-modep-of-set-eip (equal (64-bit-modep (set-eip eip x86)) (64-bit-modep x86)) :hints (("Goal" :in-theory (enable set-eip))))

(defthm 64-bit-modep-of-set-eax (equal (64-bit-modep (set-eax eax x86)) (64-bit-modep x86)) :hints (("Goal" :in-theory (enable set-eax))))
(defthm 64-bit-modep-of-set-ebx (equal (64-bit-modep (set-ebx ebx x86)) (64-bit-modep x86)) :hints (("Goal" :in-theory (enable set-ebx))))
(defthm 64-bit-modep-of-set-ecx (equal (64-bit-modep (set-ecx ecx x86)) (64-bit-modep x86)) :hints (("Goal" :in-theory (enable set-ecx))))
(defthm 64-bit-modep-of-set-edx (equal (64-bit-modep (set-edx edx x86)) (64-bit-modep x86)) :hints (("Goal" :in-theory (enable set-edx))))
(defthm 64-bit-modep-of-set-esp (equal (64-bit-modep (set-esp esp x86)) (64-bit-modep x86)) :hints (("Goal" :in-theory (enable set-esp))))
(defthm 64-bit-modep-of-set-ebp (equal (64-bit-modep (set-ebp ebp x86)) (64-bit-modep x86)) :hints (("Goal" :in-theory (enable set-ebp))))

(defthm 64-bit-modep-of-set-rax-high (equal (64-bit-modep (set-rax-high eax x86)) (64-bit-modep x86)) :hints (("Goal" :in-theory (enable set-rax-high))))
(defthm 64-bit-modep-of-set-rbx-high (equal (64-bit-modep (set-rbx-high ebx x86)) (64-bit-modep x86)) :hints (("Goal" :in-theory (enable set-rbx-high))))
(defthm 64-bit-modep-of-set-rcx-high (equal (64-bit-modep (set-rcx-high ecx x86)) (64-bit-modep x86)) :hints (("Goal" :in-theory (enable set-rcx-high))))
(defthm 64-bit-modep-of-set-rdx-high (equal (64-bit-modep (set-rdx-high edx x86)) (64-bit-modep x86)) :hints (("Goal" :in-theory (enable set-rdx-high))))
(defthm 64-bit-modep-of-set-rsp-high (equal (64-bit-modep (set-rsp-high esp x86)) (64-bit-modep x86)) :hints (("Goal" :in-theory (enable set-rsp-high))))
(defthm 64-bit-modep-of-set-rbp-high (equal (64-bit-modep (set-rbp-high ebp x86)) (64-bit-modep x86)) :hints (("Goal" :in-theory (enable set-rbp-high))))

(defthm 64-bit-modep-of-write-byte-to-segment
  (equal (64-bit-modep (write-byte-to-segment eff-addr seg-reg val x86))
         (64-bit-modep x86))
  :hints (("Goal" :in-theory (enable write-byte-to-segment))))

(defthm 64-bit-modep-of-write-to-segment
  (equal (64-bit-modep (write-to-segment n eff-addr seg-reg val x86))
         (64-bit-modep x86))
  :hints (("Goal" :in-theory (enable write-to-segment))))

(defthm 64-bit-modep-of-write-bytes-to-segment
  (equal (64-bit-modep (write-to-segment n eff-addr seg-reg val x86))
         (64-bit-modep x86)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm app-view-of-set-eip (equal (app-view (set-eip eip x86)) (app-view x86)) :hints (("Goal" :in-theory (enable set-eip))))

(defthm app-view-of-set-eax (equal (app-view (set-eax eax x86)) (app-view x86)) :hints (("Goal" :in-theory (enable set-eax))))
(defthm app-view-of-set-ebx (equal (app-view (set-ebx ebx x86)) (app-view x86)) :hints (("Goal" :in-theory (enable set-ebx))))
(defthm app-view-of-set-ecx (equal (app-view (set-ecx ecx x86)) (app-view x86)) :hints (("Goal" :in-theory (enable set-ecx))))
(defthm app-view-of-set-edx (equal (app-view (set-edx edx x86)) (app-view x86)) :hints (("Goal" :in-theory (enable set-edx))))
(defthm app-view-of-set-esp (equal (app-view (set-esp esp x86)) (app-view x86)) :hints (("Goal" :in-theory (enable set-esp))))
(defthm app-view-of-set-ebp (equal (app-view (set-ebp ebp x86)) (app-view x86)) :hints (("Goal" :in-theory (enable set-ebp))))

(defthm app-view-of-set-rax-high (equal (app-view (set-rax-high eax x86)) (app-view x86)) :hints (("Goal" :in-theory (enable set-rax-high))))
(defthm app-view-of-set-rbx-high (equal (app-view (set-rbx-high ebx x86)) (app-view x86)) :hints (("Goal" :in-theory (enable set-rbx-high))))
(defthm app-view-of-set-rcx-high (equal (app-view (set-rcx-high ecx x86)) (app-view x86)) :hints (("Goal" :in-theory (enable set-rcx-high))))
(defthm app-view-of-set-rdx-high (equal (app-view (set-rdx-high edx x86)) (app-view x86)) :hints (("Goal" :in-theory (enable set-rdx-high))))
(defthm app-view-of-set-rsp-high (equal (app-view (set-rsp-high esp x86)) (app-view x86)) :hints (("Goal" :in-theory (enable set-rsp-high))))
(defthm app-view-of-set-rbp-high (equal (app-view (set-rbp-high ebp x86)) (app-view x86)) :hints (("Goal" :in-theory (enable set-rbp-high))))

(defthm app-view-of-write-to-segment
  (equal (app-view (write-to-segment n eff-addr seg-reg val x86))
         (app-view x86)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm code-segment-assumptions32-for-code-of-set-eip
  (equal (code-segment-assumptions32-for-code code offset (set-eip eip x86))
         (code-segment-assumptions32-for-code code offset x86))
  :hints (("Goal" :in-theory (enable set-eip))))

(defthm code-segment-assumptions32-for-code-of-set-eax (equal (code-segment-assumptions32-for-code code offset (set-eax eax x86)) (code-segment-assumptions32-for-code code offset x86)) :hints (("Goal" :in-theory (enable set-eax))))
(defthm code-segment-assumptions32-for-code-of-set-ebx (equal (code-segment-assumptions32-for-code code offset (set-ebx ebx x86)) (code-segment-assumptions32-for-code code offset x86)) :hints (("Goal" :in-theory (enable set-ebx))))
(defthm code-segment-assumptions32-for-code-of-set-ecx (equal (code-segment-assumptions32-for-code code offset (set-ecx ecx x86)) (code-segment-assumptions32-for-code code offset x86)) :hints (("Goal" :in-theory (enable set-ecx))))
(defthm code-segment-assumptions32-for-code-of-set-edx (equal (code-segment-assumptions32-for-code code offset (set-edx edx x86)) (code-segment-assumptions32-for-code code offset x86)) :hints (("Goal" :in-theory (enable set-edx))))
(defthm code-segment-assumptions32-for-code-of-set-esp (equal (code-segment-assumptions32-for-code code offset (set-esp esp x86)) (code-segment-assumptions32-for-code code offset x86)) :hints (("Goal" :in-theory (enable set-esp))))
(defthm code-segment-assumptions32-for-code-of-set-ebp (equal (code-segment-assumptions32-for-code code offset (set-ebp ebp x86)) (code-segment-assumptions32-for-code code offset x86)) :hints (("Goal" :in-theory (enable set-ebp))))

(defthm code-segment-assumptions32-for-code-of-set-rax-high (equal (code-segment-assumptions32-for-code code offset (set-rax-high eax x86)) (code-segment-assumptions32-for-code code offset x86)) :hints (("Goal" :in-theory (enable set-rax-high))))
(defthm code-segment-assumptions32-for-code-of-set-rbx-high (equal (code-segment-assumptions32-for-code code offset (set-rbx-high ebx x86)) (code-segment-assumptions32-for-code code offset x86)) :hints (("Goal" :in-theory (enable set-rbx-high))))
(defthm code-segment-assumptions32-for-code-of-set-rcx-high (equal (code-segment-assumptions32-for-code code offset (set-rcx-high ecx x86)) (code-segment-assumptions32-for-code code offset x86)) :hints (("Goal" :in-theory (enable set-rcx-high))))
(defthm code-segment-assumptions32-for-code-of-set-rdx-high (equal (code-segment-assumptions32-for-code code offset (set-rdx-high edx x86)) (code-segment-assumptions32-for-code code offset x86)) :hints (("Goal" :in-theory (enable set-rdx-high))))
(defthm code-segment-assumptions32-for-code-of-set-rsp-high (equal (code-segment-assumptions32-for-code code offset (set-rsp-high esp x86)) (code-segment-assumptions32-for-code code offset x86)) :hints (("Goal" :in-theory (enable set-rsp-high))))
(defthm code-segment-assumptions32-for-code-of-set-rbp-high (equal (code-segment-assumptions32-for-code code offset (set-rbp-high ebp x86)) (code-segment-assumptions32-for-code code offset x86)) :hints (("Goal" :in-theory (enable set-rbp-high))))

(defthm code-segment-assumptions32-for-code-of-set-flag
  (equal (code-segment-assumptions32-for-code code offset (set-flag flg val x86))
         (code-segment-assumptions32-for-code code offset x86))
  :hints (("Goal" :in-theory (e/d (code-segment-assumptions32-for-code set-flag)
                                  (;; x86isa::seg-hidden-basei-is-n64p x86isa::seg-hidden-limiti-is-n32pg
                                   ;;                                  x86isa::seg-hidden-attri-is-n16p
                                   )))))

(defthm code-segment-assumptions32-for-code-of-set-undef
  (equal (code-segment-assumptions32-for-code code offset (set-undef undef x86))
         (code-segment-assumptions32-for-code code offset x86))
  :hints (("Goal" :in-theory (e/d (code-segment-assumptions32-for-code set-undef)
                                  (;; x86isa::seg-hidden-basei-is-n64p x86isa::seg-hidden-limiti-is-n32pg
                                   ;;                                  x86isa::seg-hidden-attri-is-n16p
                                   )))))

(defthm code-segment-assumptions32-for-code-of-set-mxcsr
  (equal (code-segment-assumptions32-for-code code offset (set-mxcsr mxcsr x86))
         (code-segment-assumptions32-for-code code offset x86))
  :hints (("Goal" :in-theory (e/d (code-segment-assumptions32-for-code set-mxcsr)
                                  (;; x86isa::seg-hidden-basei-is-n64p x86isa::seg-hidden-limiti-is-n32pg
                                   ;;                                  x86isa::seg-hidden-attri-is-n16p
                                   )))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm data-segment-writeable-bit-of-set-eip (equal (data-segment-writeable-bit seg-reg (set-eip eip x86)) (data-segment-writeable-bit seg-reg x86)) :hints (("Goal" :in-theory (enable set-eip))))

(defthm data-segment-writeable-bit-of-set-eax (equal (data-segment-writeable-bit seg-reg (set-eax eax x86)) (data-segment-writeable-bit seg-reg x86)) :hints (("Goal" :in-theory (enable set-eax))))
(defthm data-segment-writeable-bit-of-set-ebx (equal (data-segment-writeable-bit seg-reg (set-ebx ebx x86)) (data-segment-writeable-bit seg-reg x86)) :hints (("Goal" :in-theory (enable set-ebx))))
(defthm data-segment-writeable-bit-of-set-ecx (equal (data-segment-writeable-bit seg-reg (set-ecx ecx x86)) (data-segment-writeable-bit seg-reg x86)) :hints (("Goal" :in-theory (enable set-ecx))))
(defthm data-segment-writeable-bit-of-set-edx (equal (data-segment-writeable-bit seg-reg (set-edx edx x86)) (data-segment-writeable-bit seg-reg x86)) :hints (("Goal" :in-theory (enable set-edx))))
(defthm data-segment-writeable-bit-of-set-esp (equal (data-segment-writeable-bit seg-reg (set-esp esp x86)) (data-segment-writeable-bit seg-reg x86)) :hints (("Goal" :in-theory (enable set-esp))))
(defthm data-segment-writeable-bit-of-set-ebp (equal (data-segment-writeable-bit seg-reg (set-ebp ebp x86)) (data-segment-writeable-bit seg-reg x86)) :hints (("Goal" :in-theory (enable set-ebp))))

(defthm data-segment-writeable-bit-of-set-rax-high (equal (data-segment-writeable-bit seg-reg (set-rax-high eax x86)) (data-segment-writeable-bit seg-reg x86)) :hints (("Goal" :in-theory (enable set-rax-high))))
(defthm data-segment-writeable-bit-of-set-rbx-high (equal (data-segment-writeable-bit seg-reg (set-rbx-high ebx x86)) (data-segment-writeable-bit seg-reg x86)) :hints (("Goal" :in-theory (enable set-rbx-high))))
(defthm data-segment-writeable-bit-of-set-rcx-high (equal (data-segment-writeable-bit seg-reg (set-rcx-high ecx x86)) (data-segment-writeable-bit seg-reg x86)) :hints (("Goal" :in-theory (enable set-rcx-high))))
(defthm data-segment-writeable-bit-of-set-rdx-high (equal (data-segment-writeable-bit seg-reg (set-rdx-high edx x86)) (data-segment-writeable-bit seg-reg x86)) :hints (("Goal" :in-theory (enable set-rdx-high))))
(defthm data-segment-writeable-bit-of-set-rsp-high (equal (data-segment-writeable-bit seg-reg (set-rsp-high esp x86)) (data-segment-writeable-bit seg-reg x86)) :hints (("Goal" :in-theory (enable set-rsp-high))))
(defthm data-segment-writeable-bit-of-set-rbp-high (equal (data-segment-writeable-bit seg-reg (set-rbp-high ebp x86)) (data-segment-writeable-bit seg-reg x86)) :hints (("Goal" :in-theory (enable set-rbp-high))))

(defthm data-segment-writeable-bit-of-write-byte-to-segment
  (equal (data-segment-writeable-bit seg-reg1 (write-byte-to-segment eff-addr seg-reg2 val x86))
         (data-segment-writeable-bit seg-reg1 x86))
  :hints (("Goal" :in-theory (enable write-byte-to-segment))))

(defthm data-segment-writeable-bit-of-write-to-segment
  (equal (data-segment-writeable-bit seg-reg1 (write-to-segment n eff-addr seg-reg2 val x86))
         (data-segment-writeable-bit seg-reg1 x86))
  :hints (("Goal" :in-theory (enable write-to-segment))))

(defthm data-segment-writeable-bit-of-set-flag
  (equal (data-segment-writeable-bit seg-reg (set-flag flg val x86))
         (data-segment-writeable-bit seg-reg x86))
  :hints (("Goal" :in-theory (e/d (data-segment-writeable-bit) (data-segment-writeable-bit-intro)))))

(defthm data-segment-writeable-bit-of-set-undef
  (equal (data-segment-writeable-bit seg-reg (set-undef undef x86))
         (data-segment-writeable-bit seg-reg x86))
  :hints (("Goal" :in-theory (e/d (data-segment-writeable-bit) (data-segment-writeable-bit-intro)))))

(defthm data-segment-writeable-bit-of-set-mxcsr
  (equal (data-segment-writeable-bit seg-reg (set-mxcsr mxcsr x86))
         (data-segment-writeable-bit seg-reg x86))
  :hints (("Goal" :in-theory (e/d (data-segment-writeable-bit) (data-segment-writeable-bit-intro)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm code-segment-readable-bit-of-set-eip (equal (code-segment-readable-bit (set-eip eip x86)) (code-segment-readable-bit x86)) :hints (("Goal" :in-theory (enable set-eip))))

(defthm code-segment-readable-bit-of-set-eax (equal (code-segment-readable-bit (set-eax eax x86)) (code-segment-readable-bit x86)) :hints (("Goal" :in-theory (enable set-eax))))
(defthm code-segment-readable-bit-of-set-ebx (equal (code-segment-readable-bit (set-ebx ebx x86)) (code-segment-readable-bit x86)) :hints (("Goal" :in-theory (enable set-ebx))))
(defthm code-segment-readable-bit-of-set-ecx (equal (code-segment-readable-bit (set-ecx ecx x86)) (code-segment-readable-bit x86)) :hints (("Goal" :in-theory (enable set-ecx))))
(defthm code-segment-readable-bit-of-set-edx (equal (code-segment-readable-bit (set-edx edx x86)) (code-segment-readable-bit x86)) :hints (("Goal" :in-theory (enable set-edx))))
(defthm code-segment-readable-bit-of-set-esp (equal (code-segment-readable-bit (set-esp esp x86)) (code-segment-readable-bit x86)) :hints (("Goal" :in-theory (enable set-esp))))
(defthm code-segment-readable-bit-of-set-ebp (equal (code-segment-readable-bit (set-ebp ebp x86)) (code-segment-readable-bit x86)) :hints (("Goal" :in-theory (enable set-ebp))))

(defthm code-segment-readable-bit-of-set-rax-high (equal (code-segment-readable-bit (set-rax-high eax x86)) (code-segment-readable-bit x86)) :hints (("Goal" :in-theory (enable set-rax-high))))
(defthm code-segment-readable-bit-of-set-rbx-high (equal (code-segment-readable-bit (set-rbx-high ebx x86)) (code-segment-readable-bit x86)) :hints (("Goal" :in-theory (enable set-rbx-high))))
(defthm code-segment-readable-bit-of-set-rcx-high (equal (code-segment-readable-bit (set-rcx-high ecx x86)) (code-segment-readable-bit x86)) :hints (("Goal" :in-theory (enable set-rcx-high))))
(defthm code-segment-readable-bit-of-set-rdx-high (equal (code-segment-readable-bit (set-rdx-high edx x86)) (code-segment-readable-bit x86)) :hints (("Goal" :in-theory (enable set-rdx-high))))
(defthm code-segment-readable-bit-of-set-rsp-high (equal (code-segment-readable-bit (set-rsp-high esp x86)) (code-segment-readable-bit x86)) :hints (("Goal" :in-theory (enable set-rsp-high))))
(defthm code-segment-readable-bit-of-set-rbp-high (equal (code-segment-readable-bit (set-rbp-high ebp x86)) (code-segment-readable-bit x86)) :hints (("Goal" :in-theory (enable set-rbp-high))))

(defthm code-segment-readable-bit-of-write-byte-to-segment
  (equal (code-segment-readable-bit (write-byte-to-segment eff-addr seg-reg2 val x86))
         (code-segment-readable-bit x86))
  :hints (("Goal" :in-theory (enable write-byte-to-segment))))

(defthm code-segment-readable-bit-of-write-to-segment
  (equal (code-segment-readable-bit (write-to-segment n eff-addr seg-reg2 val x86))
         (code-segment-readable-bit x86))
  :hints (("Goal" :in-theory (enable write-to-segment))))

(defthm code-segment-readable-bit-of-set-flag
  (equal (code-segment-readable-bit (set-flag flg val x86))
         (code-segment-readable-bit x86))
  :hints (("Goal" :in-theory (e/d (code-segment-readable-bit) (code-segment-readable-bit-intro)))))

(defthm code-segment-readable-bit-of-set-undef
  (equal (code-segment-readable-bit (set-undef undex x86))
         (code-segment-readable-bit x86))
  :hints (("Goal" :in-theory (e/d (code-segment-readable-bit) (code-segment-readable-bit-intro)))))

(defthm code-segment-readable-bit-of-set-mxcsr
  (equal (code-segment-readable-bit (set-mxcsr undex x86))
         (code-segment-readable-bit x86))
  :hints (("Goal" :in-theory (e/d (code-segment-readable-bit) (code-segment-readable-bit-intro)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm code-segment-well-formedp-of-set-eip
  (equal (code-segment-well-formedp (set-eip eip x86))
         (code-segment-well-formedp x86))
  :hints (("Goal" :in-theory (enable set-eip))))

(defthm code-segment-well-formedp-of-set-eax (equal (code-segment-well-formedp (set-eax eax x86)) (code-segment-well-formedp x86)) :hints (("Goal" :in-theory (enable set-eax))))
(defthm code-segment-well-formedp-of-set-ebx (equal (code-segment-well-formedp (set-ebx ebx x86)) (code-segment-well-formedp x86)) :hints (("Goal" :in-theory (enable set-ebx))))
(defthm code-segment-well-formedp-of-set-ecx (equal (code-segment-well-formedp (set-ecx ecx x86)) (code-segment-well-formedp x86)) :hints (("Goal" :in-theory (enable set-ecx))))
(defthm code-segment-well-formedp-of-set-edx (equal (code-segment-well-formedp (set-edx edx x86)) (code-segment-well-formedp x86)) :hints (("Goal" :in-theory (enable set-edx))))
(defthm code-segment-well-formedp-of-set-esp (equal (code-segment-well-formedp (set-esp esp x86)) (code-segment-well-formedp x86)) :hints (("Goal" :in-theory (enable set-esp))))
(defthm code-segment-well-formedp-of-set-ebp (equal (code-segment-well-formedp (set-ebp ebp x86)) (code-segment-well-formedp x86)) :hints (("Goal" :in-theory (enable set-ebp))))

(defthm code-segment-well-formedp-of-set-rax-high (equal (code-segment-well-formedp (set-rax-high eax x86)) (code-segment-well-formedp x86)) :hints (("Goal" :in-theory (enable set-rax-high))))
(defthm code-segment-well-formedp-of-set-rbx-high (equal (code-segment-well-formedp (set-rbx-high ebx x86)) (code-segment-well-formedp x86)) :hints (("Goal" :in-theory (enable set-rbx-high))))
(defthm code-segment-well-formedp-of-set-rcx-high (equal (code-segment-well-formedp (set-rcx-high ecx x86)) (code-segment-well-formedp x86)) :hints (("Goal" :in-theory (enable set-rcx-high))))
(defthm code-segment-well-formedp-of-set-rdx-high (equal (code-segment-well-formedp (set-rdx-high edx x86)) (code-segment-well-formedp x86)) :hints (("Goal" :in-theory (enable set-rdx-high))))
(defthm code-segment-well-formedp-of-set-rsp-high (equal (code-segment-well-formedp (set-rsp-high esp x86)) (code-segment-well-formedp x86)) :hints (("Goal" :in-theory (enable set-rsp-high))))
(defthm code-segment-well-formedp-of-set-rbp-high (equal (code-segment-well-formedp (set-rbp-high ebp x86)) (code-segment-well-formedp x86)) :hints (("Goal" :in-theory (enable set-rbp-high))))

(defthm code-segment-well-formedp-of-write-to-segment
  (equal (code-segment-well-formedp (write-to-segment n eff-addr seg-reg val x86))
         (code-segment-well-formedp x86))
  :hints (("Goal" :in-theory (enable code-segment-well-formedp
                                     code-and-stack-segments-separate
                                     32-bit-segment-size))))

(defthm code-segment-well-formedp-of-set-flag
  (equal (code-segment-well-formedp (set-flag flg val x86))
         (code-segment-well-formedp x86))
  :hints (("Goal" :in-theory (e/d (code-segment-well-formedp set-flag)
                                  (;; x86isa::seg-hidden-basei-is-n64p x86isa::seg-hidden-limiti-is-n32p
                                   ;;                                  x86isa::seg-hidden-attri-is-n16p
                                   )))))

(defthm code-segment-well-formedp-of-set-mxcsr
  (equal (code-segment-well-formedp (set-mxcsr mxcsr x86))
         (code-segment-well-formedp x86))
  :hints (("Goal" :in-theory (e/d (code-segment-well-formedp set-mxcsr)
                                  (;; x86isa::seg-hidden-basei-is-n64p x86isa::seg-hidden-limiti-is-n32p
                                   ;;                                  x86isa::seg-hidden-attri-is-n16p
                                   )))))

(defthm code-segment-well-formedp-of-set-undef
  (equal (code-segment-well-formedp (set-undef undef x86))
         (code-segment-well-formedp x86))
  :hints (("Goal" :in-theory (e/d (code-segment-well-formedp set-undef)
                                  (;; x86isa::seg-hidden-basei-is-n64p x86isa::seg-hidden-limiti-is-n32p
                                   ;;                                  x86isa::seg-hidden-attri-is-n16p
                                   )))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm stack-segment-assumptions32-of-write-to-segment
  (equal (stack-segment-assumptions32 stack-slots-needed (write-to-segment n eff-addr seg-reg val x86))
         (stack-segment-assumptions32 stack-slots-needed x86))
  :hints (("Goal" :in-theory (e/d () (;; x86isa::rgfi-is-i64p
                                      ;; x86isa::seg-hidden-basei-is-n64p
                                      ;; x86isa::seg-hidden-limiti-is-n32p
                                      ;; x86isa::seg-hidden-attri-is-n16p
                                      ))))) ;bad forcing

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm read-byte-from-segment-of-write-to-segment-diff-segments
  (implies (and (segments-separate seg-reg1 seg-reg2 x86)
                (eff-addr-okp eff-addr1 seg-reg1 x86)
                (eff-addrs-okp n2 eff-addr2 seg-reg2 x86)
                (seg-regp seg-reg1)
                (seg-regp seg-reg2)
                (segment-is-32-bitsp seg-reg1 x86)
                (segment-is-32-bitsp seg-reg2 x86)
                (x86p x86)
                (not (64-bit-modep x86))
                (natp eff-addr1)
                (natp eff-addr2)
                (well-formed-32-bit-segmentp seg-reg1 x86)
                (well-formed-32-bit-segmentp seg-reg2 x86))
           (equal (read-byte-from-segment eff-addr1 seg-reg1 (write-to-segment n2 eff-addr2 seg-reg2 val x86))
                  (read-byte-from-segment eff-addr1 seg-reg1 x86)))
  :hints (("Goal" :in-theory (enable write-to-segment
                                     segment-min-eff-addr32
                                     segment-max-eff-addr32))))

(defthm read-byte-list-from-segment-of-write-to-segment-diff-segments
  (implies (and (segments-separate seg-reg1 seg-reg2 x86)
                (eff-addrs-okp n1 eff-addr1 seg-reg1 x86)
                (eff-addrs-okp n2 eff-addr2 seg-reg2 x86)
                (seg-regp seg-reg1)
                (seg-regp seg-reg2)
                (segment-is-32-bitsp seg-reg1 x86)
                (segment-is-32-bitsp seg-reg2 x86)
                (< n1 (expt 2 32))
                (natp eff-addr1)
                (natp eff-addr2)
                (natp n2)
                (not (64-bit-modep x86))
;                (not (equal seg-reg1 seg-reg2))
                ;; (< (+ -1 n1 eff-addr1) (32-bit-segment-size seg-reg1 x86))
                ;; (< (+ -1 n2 eff-addr2) (32-bit-segment-size seg-reg2 x86))
                (well-formed-32-bit-segmentp seg-reg1 x86)
                (well-formed-32-bit-segmentp seg-reg2 x86)
                (x86p x86))
           (equal (read-byte-list-from-segment n1 eff-addr1 seg-reg1 (write-to-segment n2 eff-addr2 seg-reg2 val x86))
                  (read-byte-list-from-segment n1 eff-addr1 seg-reg1 x86)))
  :hints (("Goal" :expand (;(write-to-segment n eff-addr seg-reg2 val x86)
                           ;;(READ-BYTE-FROM-SEGMENT EFF-ADDR1 SEG-REG1 X86)
                           )
           :induct (READ-BYTE-LIST-FROM-SEGMENT N1 EFF-ADDR1 SEG-REG1 X86)
           :in-theory (e/d (read-byte-list-from-segment
                              write-to-segment
                              write-to-segment-of-write-byte-to-segment)
                           (READ-BYTE-FROM-SEGMENT)))))

(defthm code-segment-assumptions32-for-code-of-write-to-segment
  (implies (and (segments-separate *cs* seg-reg x86)
                (seg-regp seg-reg)
                (segment-is-32-bitsp seg-reg x86)
                (< (len code) 4294967296)
                (natp eff-addr)
                (natp n)
                (<= (len code) (32-bit-segment-size *cs* x86))
                (< 0 (32-bit-segment-size seg-reg x86)) ;drop?
                ;(< (+ -1 n eff-addr) (32-bit-segment-size seg-reg x86)) ;gen
                (eff-addrs-okp n eff-addr seg-reg x86)
                (code-segment-well-formedp x86)
                ;(well-formed-32-bit-segmentp *cs* x86)
                (well-formed-32-bit-segmentp seg-reg x86)
                (not (64-bit-modep x86))
                (natp offset)
                (x86p x86))
           (equal (code-segment-assumptions32-for-code code offset (write-to-segment n eff-addr seg-reg val x86))
                  (code-segment-assumptions32-for-code code offset x86)))
  :hints (("Goal" :in-theory (enable code-segment-assumptions32-for-code
                                     code-and-stack-segments-separate 32-bit-segment-size))))

(defthm read-from-segment-of-write-to-segment-diff-segments
  (implies (and (segments-separate seg-reg1 seg-reg2 x86)
                (eff-addrs-okp n1 eff-addr1 seg-reg1 x86)
                (eff-addrs-okp n2 eff-addr2 seg-reg2 x86)
                (seg-regp seg-reg1)
                (seg-regp seg-reg2)
                (segment-is-32-bitsp seg-reg1 x86)
                (segment-is-32-bitsp seg-reg2 x86)
                (x86p x86)
                (not (64-bit-modep x86))
                (natp eff-addr1)
                (natp eff-addr2)
                (well-formed-32-bit-segmentp seg-reg1 x86)
                (well-formed-32-bit-segmentp seg-reg2 x86))
           (equal (read-from-segment n1 eff-addr1 seg-reg1 (write-to-segment n2 eff-addr2 seg-reg2 val x86))
                  (read-from-segment n1 eff-addr1 seg-reg1 x86)))
  :hints (("Goal" :in-theory (enable write-to-segment
                                     segment-min-eff-addr32
                                     segment-max-eff-addr32))))


;move?
(defthm write-to-segment-of-write-byte-to-segment-included
  (implies (and (integerp eff-addr1)
                (integerp eff-addr2)
                (<= eff-addr1 eff-addr2)
                (< eff-addr2 (+ eff-addr1 n)) ;not a cyclic range...
                (unsigned-byte-p 32 n)
                (x86p x86))
           (equal (write-to-segment n eff-addr1 seg-reg val1 (write-byte-to-segment eff-addr2 seg-reg val2 x86))
                  (write-to-segment n eff-addr1 seg-reg val1 x86)))
  :hints (
          ("Goal" :induct (write-to-segment n eff-addr1 seg-reg val1 x86)
           :in-theory (e/d (sep-eff-addr-ranges-swap
                            write-to-segment
                            unsigned-byte-p)
                           (sep-eff-addr-ranges
                            acl2::bvcat-equal-rewrite-alt

                            acl2::bvcat-equal-rewrite)))))

(defthm write-to-segment-of-write-to-segment-included
  (implies (and (integerp eff-addr1)
                (integerp eff-addr2)
                (<= eff-addr1 eff-addr2)
                (<= (+ eff-addr2 n2) (+ eff-addr1 n1)) ;not a cyclic range...
                (unsigned-byte-p 32 n1)
                (unsigned-byte-p 32 n2)
                (x86p x86))
           (equal (write-to-segment n1 eff-addr1 seg-reg val1 (write-to-segment n2 eff-addr2 seg-reg val2 x86))
                  (write-to-segment n1 eff-addr1 seg-reg val1 x86)))
  :hints (("Goal" :induct (write-to-segment n2 eff-addr2 seg-reg val2 x86)
           :in-theory (e/d (sep-eff-addr-ranges-swap
                            write-to-segment
                            unsigned-byte-p)
                           (sep-eff-addr-ranges
                            acl2::bvcat-equal-rewrite-alt

                            acl2::bvcat-equal-rewrite)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm read-stack-dword-of-set-eip (equal (read-stack-dword eff-addr (set-eip val x86)) (read-stack-dword eff-addr x86)) :hints (("Goal" :in-theory (enable set-eip))))

(defthm read-stack-dword-of-set-eax (equal (read-stack-dword eff-addr (set-eax val x86)) (read-stack-dword eff-addr x86)) :hints (("Goal" :in-theory (enable set-eax))))
(defthm read-stack-dword-of-set-ebx (equal (read-stack-dword eff-addr (set-ebx val x86)) (read-stack-dword eff-addr x86)) :hints (("Goal" :in-theory (enable set-ebx))))
(defthm read-stack-dword-of-set-ecx (equal (read-stack-dword eff-addr (set-ecx val x86)) (read-stack-dword eff-addr x86)) :hints (("Goal" :in-theory (enable set-ecx))))
(defthm read-stack-dword-of-set-edx (equal (read-stack-dword eff-addr (set-edx val x86)) (read-stack-dword eff-addr x86)) :hints (("Goal" :in-theory (enable set-edx))))
(defthm read-stack-dword-of-set-esp (equal (read-stack-dword eff-addr (set-esp val x86)) (read-stack-dword eff-addr x86)) :hints (("Goal" :in-theory (enable set-esp))))
(defthm read-stack-dword-of-set-ebp (equal (read-stack-dword eff-addr (set-ebp val x86)) (read-stack-dword eff-addr x86)) :hints (("Goal" :in-theory (enable set-ebp))))

(defthm read-stack-dword-of-set-rax-high (equal (read-stack-dword eff-addr (set-rax-high val x86)) (read-stack-dword eff-addr x86)) :hints (("Goal" :in-theory (enable set-rax-high))))
(defthm read-stack-dword-of-set-rbx-high (equal (read-stack-dword eff-addr (set-rbx-high val x86)) (read-stack-dword eff-addr x86)) :hints (("Goal" :in-theory (enable set-rbx-high))))
(defthm read-stack-dword-of-set-rcx-high (equal (read-stack-dword eff-addr (set-rcx-high val x86)) (read-stack-dword eff-addr x86)) :hints (("Goal" :in-theory (enable set-rcx-high))))
(defthm read-stack-dword-of-set-rdx-high (equal (read-stack-dword eff-addr (set-rdx-high val x86)) (read-stack-dword eff-addr x86)) :hints (("Goal" :in-theory (enable set-rdx-high))))
(defthm read-stack-dword-of-set-rsp-high (equal (read-stack-dword eff-addr (set-rsp-high val x86)) (read-stack-dword eff-addr x86)) :hints (("Goal" :in-theory (enable set-rsp-high))))
(defthm read-stack-dword-of-set-rbp-high (equal (read-stack-dword eff-addr (set-rbp-high val x86)) (read-stack-dword eff-addr x86)) :hints (("Goal" :in-theory (enable set-rbp-high))))

(local (in-theory (disable read-stack-dword-intro)))

;move?
(defthm read-stack-dword-of-write-to-segment-diff-segments
  (implies (and (segments-separate *ss* seg-reg2 x86)
                (eff-addrs-okp 4 eff-addr1 *ss* x86)
                (eff-addrs-okp n2 eff-addr2 seg-reg2 x86)
                (seg-regp seg-reg2)
                (segment-is-32-bitsp *ss* x86)
                (segment-is-32-bitsp seg-reg2 x86)
                (x86p x86)
                (not (64-bit-modep x86))
                (natp eff-addr1)
                (natp eff-addr2)
                (well-formed-32-bit-segmentp *ss* x86)
                (well-formed-32-bit-segmentp seg-reg2 x86))
           (equal (read-stack-dword eff-addr1 (write-to-segment n2 eff-addr2 seg-reg2 val x86))
                  (read-stack-dword eff-addr1 x86)))
  :hints (("Goal" :in-theory (enable read-stack-dword))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm eax-of-set-flag (equal (eax (set-flag flag val x86)) (eax x86)) :hints (("Goal" :in-theory (enable set-flag))))
(defthm ebx-of-set-flag (equal (ebx (set-flag flag val x86)) (ebx x86)) :hints (("Goal" :in-theory (enable set-flag))))
(defthm ecx-of-set-flag (equal (ecx (set-flag flag val x86)) (ecx x86)) :hints (("Goal" :in-theory (enable set-flag))))
(defthm edx-of-set-flag (equal (edx (set-flag flag val x86)) (edx x86)) :hints (("Goal" :in-theory (enable set-flag))))
(defthm ebp-of-set-flag (equal (ebp (set-flag flag val x86)) (ebp x86)) :hints (("Goal" :in-theory (enable set-flag))))
(defthm esp-of-set-flag (equal (esp (set-flag flag val x86)) (esp x86)) :hints (("Goal" :in-theory (enable set-flag))))
;; (defthm esi-of-set-flag (equal (esi (set-flag flag val x86)) (esi x86)) :hints (("Goal" :in-theory (enable set-flag))))
;; (defthm edi-of-set-flag (equal (edi (set-flag flag val x86)) (edi x86)) :hints (("Goal" :in-theory (enable set-flag))))
;;todo: more?

(defthm eax-of-set-undef (equal (eax (set-undef undef x86)) (eax x86)) :hints (("Goal" :in-theory (enable set-undef))))
(defthm ebx-of-set-undef (equal (ebx (set-undef undef x86)) (ebx x86)) :hints (("Goal" :in-theory (enable set-undef))))
(defthm ecx-of-set-undef (equal (ecx (set-undef undef x86)) (ecx x86)) :hints (("Goal" :in-theory (enable set-undef))))
(defthm edx-of-set-undef (equal (edx (set-undef undef x86)) (edx x86)) :hints (("Goal" :in-theory (enable set-undef))))
(defthm ebp-of-set-undef (equal (ebp (set-undef undef x86)) (ebp x86)) :hints (("Goal" :in-theory (enable set-undef))))
(defthm esp-of-set-undef (equal (esp (set-undef undef x86)) (esp x86)) :hints (("Goal" :in-theory (enable set-undef))))
;; (defthm esi-of-set-undef (equal (esi (set-undef undef x86)) (esi x86)) :hints (("Goal" :in-theory (enable set-undef))))
;; (defthm edi-of-set-undef (equal (edi (set-undef undef x86)) (edi x86)) :hints (("Goal" :in-theory (enable set-undef))))
;todo: more?

(defthm eax-of-set-mxcsr (equal (eax (set-mxcsr mxcsr x86)) (eax x86)) :hints (("Goal" :in-theory (enable set-mxcsr))))
(defthm ebx-of-set-mxcsr (equal (ebx (set-mxcsr mxcsr x86)) (ebx x86)) :hints (("Goal" :in-theory (enable set-mxcsr))))
(defthm ecx-of-set-mxcsr (equal (ecx (set-mxcsr mxcsr x86)) (ecx x86)) :hints (("Goal" :in-theory (enable set-mxcsr))))
(defthm edx-of-set-mxcsr (equal (edx (set-mxcsr mxcsr x86)) (edx x86)) :hints (("Goal" :in-theory (enable set-mxcsr))))
(defthm ebp-of-set-mxcsr (equal (ebp (set-mxcsr mxcsr x86)) (ebp x86)) :hints (("Goal" :in-theory (enable set-mxcsr))))
(defthm esp-of-set-mxcsr (equal (esp (set-mxcsr mxcsr x86)) (esp x86)) :hints (("Goal" :in-theory (enable set-mxcsr))))
;; (defthm esi-of-set-mxcsr (equal (esi (set-mxcsr mxcsr x86)) (esi x86)) :hints (("Goal" :in-theory (enable set-mxcsr))))
;; (defthm edi-of-set-mxcsr (equal (edi (set-mxcsr mxcsr x86)) (edi x86)) :hints (("Goal" :in-theory (enable set-mxcsr))))
;todo: more?


(defthm rax-high-of-set-flag (equal (rax-high (set-flag flag val x86)) (rax-high x86)) :hints (("Goal" :in-theory (enable set-flag))))
(defthm rbx-high-of-set-flag (equal (rbx-high (set-flag flag val x86)) (rbx-high x86)) :hints (("Goal" :in-theory (enable set-flag))))
(defthm rcx-high-of-set-flag (equal (rcx-high (set-flag flag val x86)) (rcx-high x86)) :hints (("Goal" :in-theory (enable set-flag))))
(defthm rdx-high-of-set-flag (equal (rdx-high (set-flag flag val x86)) (rdx-high x86)) :hints (("Goal" :in-theory (enable set-flag))))
(defthm rbp-high-of-set-flag (equal (rbp-high (set-flag flag val x86)) (rbp-high x86)) :hints (("Goal" :in-theory (enable set-flag))))
(defthm rsp-high-of-set-flag (equal (rsp-high (set-flag flag val x86)) (rsp-high x86)) :hints (("Goal" :in-theory (enable set-flag))))
;; (defthm esi-of-set-flag (equal (esi (set-flag flag val x86)) (esi x86)) :hints (("Goal" :in-theory (enable set-flag))))
;; (defthm edi-of-set-flag (equal (edi (set-flag flag val x86)) (edi x86)) :hints (("Goal" :in-theory (enable set-flag))))
;;todo: more?

(defthm rax-high-of-set-undef (equal (rax-high (set-undef undef x86)) (rax-high x86)) :hints (("Goal" :in-theory (enable set-undef))))
(defthm rbx-high-of-set-undef (equal (rbx-high (set-undef undef x86)) (rbx-high x86)) :hints (("Goal" :in-theory (enable set-undef))))
(defthm rcx-high-of-set-undef (equal (rcx-high (set-undef undef x86)) (rcx-high x86)) :hints (("Goal" :in-theory (enable set-undef))))
(defthm rdx-high-of-set-undef (equal (rdx-high (set-undef undef x86)) (rdx-high x86)) :hints (("Goal" :in-theory (enable set-undef))))
(defthm rbp-high-of-set-undef (equal (rbp-high (set-undef undef x86)) (rbp-high x86)) :hints (("Goal" :in-theory (enable set-undef))))
(defthm rsp-high-of-set-undef (equal (rsp-high (set-undef undef x86)) (rsp-high x86)) :hints (("Goal" :in-theory (enable set-undef))))
;; (defthm esi-of-set-undef (equal (esi (set-undef undef x86)) (esi x86)) :hints (("Goal" :in-theory (enable set-undef))))
;; (defthm edi-of-set-undef (equal (edi (set-undef undef x86)) (edi x86)) :hints (("Goal" :in-theory (enable set-undef))))
;todo: more?

(defthm rax-high-of-set-mxcsr (equal (rax-high (set-mxcsr mxcsr x86)) (rax-high x86)) :hints (("Goal" :in-theory (enable set-mxcsr))))
(defthm rbx-high-of-set-mxcsr (equal (rbx-high (set-mxcsr mxcsr x86)) (rbx-high x86)) :hints (("Goal" :in-theory (enable set-mxcsr))))
(defthm rcx-high-of-set-mxcsr (equal (rcx-high (set-mxcsr mxcsr x86)) (rcx-high x86)) :hints (("Goal" :in-theory (enable set-mxcsr))))
(defthm rdx-high-of-set-mxcsr (equal (rdx-high (set-mxcsr mxcsr x86)) (rdx-high x86)) :hints (("Goal" :in-theory (enable set-mxcsr))))
(defthm rbp-high-of-set-mxcsr (equal (rbp-high (set-mxcsr mxcsr x86)) (rbp-high x86)) :hints (("Goal" :in-theory (enable set-mxcsr))))
(defthm rsp-high-of-set-mxcsr (equal (rsp-high (set-mxcsr mxcsr x86)) (rsp-high x86)) :hints (("Goal" :in-theory (enable set-mxcsr))))
;; (defthm esi-of-set-mxcsr (equal (esi (set-mxcsr mxcsr x86)) (esi x86)) :hints (("Goal" :in-theory (enable set-mxcsr))))
;; (defthm edi-of-set-mxcsr (equal (edi (set-mxcsr mxcsr x86)) (edi x86)) :hints (("Goal" :in-theory (enable set-mxcsr))))
;todo: more?




;;(defthm undef-of-set-reg-high (equal (undef (set-reg-high reg val x86)) (undef x86)) :hints (("Goal" :in-theory (enable undef set-reg-high))))
(defthm undef-of-set-eip (equal (undef (set-eip val x86)) (undef x86)) :hints (("Goal" :in-theory (enable undef set-eip))))
(defthm undef-of-set-eax (equal (undef (set-eax val x86)) (undef x86)) :hints (("Goal" :in-theory (enable undef set-eax))))
(defthm undef-of-set-ebx (equal (undef (set-ebx val x86)) (undef x86)) :hints (("Goal" :in-theory (enable undef set-ebx))))
(defthm undef-of-set-ecx (equal (undef (set-ecx val x86)) (undef x86)) :hints (("Goal" :in-theory (enable undef set-ecx))))
(defthm undef-of-set-edx (equal (undef (set-edx val x86)) (undef x86)) :hints (("Goal" :in-theory (enable undef set-edx))))
;; (defthm undef-of-set-esi (equal (undef (set-esi val x86)) (undef x86)) :hints (("Goal" :in-theory (enable undef set-esi))))
;; (defthm undef-of-set-edi (equal (undef (set-edi val x86)) (undef x86)) :hints (("Goal" :in-theory (enable undef set-edi))))
(defthm undef-of-set-esp (equal (undef (set-esp val x86)) (undef x86)) :hints (("Goal" :in-theory (enable undef set-esp))))
(defthm undef-of-set-ebp (equal (undef (set-ebp val x86)) (undef x86)) :hints (("Goal" :in-theory (enable undef set-ebp))))

;(defthm undef-of-set-rip-high (equal (undef (set-rip-high val x86)) (undef x86)) :hints (("Goal" :in-theory (enable undef set-rip-high))))
(defthm undef-of-set-rax-high (equal (undef (set-rax-high val x86)) (undef x86)) :hints (("Goal" :in-theory (enable undef set-rax-high))))
(defthm undef-of-set-rbx-high (equal (undef (set-rbx-high val x86)) (undef x86)) :hints (("Goal" :in-theory (enable undef set-rbx-high))))
(defthm undef-of-set-rcx-high (equal (undef (set-rcx-high val x86)) (undef x86)) :hints (("Goal" :in-theory (enable undef set-rcx-high))))
(defthm undef-of-set-rdx-high (equal (undef (set-rdx-high val x86)) (undef x86)) :hints (("Goal" :in-theory (enable undef set-rdx-high))))
;; (defthm undef-of-set-rsi-high (equal (undef (set-rsi-high val x86)) (undef x86)) :hints (("Goal" :in-theory (enable undef set-rsi-high))))
;; (defthm undef-of-set-rdi-high (equal (undef (set-rdi-high val x86)) (undef x86)) :hints (("Goal" :in-theory (enable undef set-rdi-high))))
(defthm undef-of-set-rsp-high (equal (undef (set-rsp-high val x86)) (undef x86)) :hints (("Goal" :in-theory (enable undef set-rsp-high))))
(defthm undef-of-set-rbp-high (equal (undef (set-rbp-high val x86)) (undef x86)) :hints (("Goal" :in-theory (enable undef set-rbp-high))))

;;(defthm mxcsr-of-set-reg-high (equal (mxcsr (set-reg-high reg val x86)) (mxcsr x86)) :hints (("Goal" :in-theory (enable mxcsr set-reg-high))))
(defthm mxcsr-of-set-eip (equal (mxcsr (set-eip val x86)) (mxcsr x86)) :hints (("Goal" :in-theory (enable mxcsr set-eip))))
(defthm mxcsr-of-set-eax (equal (mxcsr (set-eax val x86)) (mxcsr x86)) :hints (("Goal" :in-theory (enable mxcsr set-eax))))
(defthm mxcsr-of-set-ebx (equal (mxcsr (set-ebx val x86)) (mxcsr x86)) :hints (("Goal" :in-theory (enable mxcsr set-ebx))))
(defthm mxcsr-of-set-ecx (equal (mxcsr (set-ecx val x86)) (mxcsr x86)) :hints (("Goal" :in-theory (enable mxcsr set-ecx))))
(defthm mxcsr-of-set-edx (equal (mxcsr (set-edx val x86)) (mxcsr x86)) :hints (("Goal" :in-theory (enable mxcsr set-edx))))
;; (defthm mxcsr-of-set-esi (equal (mxcsr (set-esi val x86)) (mxcsr x86)) :hints (("Goal" :in-theory (enable mxcsr set-esi))))
;; (defthm mxcsr-of-set-edi (equal (mxcsr (set-edi val x86)) (mxcsr x86)) :hints (("Goal" :in-theory (enable mxcsr set-edi))))
(defthm mxcsr-of-set-esp (equal (mxcsr (set-esp val x86)) (mxcsr x86)) :hints (("Goal" :in-theory (enable mxcsr set-esp))))
(defthm mxcsr-of-set-ebp (equal (mxcsr (set-ebp val x86)) (mxcsr x86)) :hints (("Goal" :in-theory (enable mxcsr set-ebp))))

;(defthm mxcsr-of-set-rip-high (equal (mxcsr (set-rip-high val x86)) (mxcsr x86)) :hints (("Goal" :in-theory (enable mxcsr set-rip-high))))
(defthm mxcsr-of-set-rax-high (equal (mxcsr (set-rax-high val x86)) (mxcsr x86)) :hints (("Goal" :in-theory (enable mxcsr set-rax-high))))
(defthm mxcsr-of-set-rbx-high (equal (mxcsr (set-rbx-high val x86)) (mxcsr x86)) :hints (("Goal" :in-theory (enable mxcsr set-rbx-high))))
(defthm mxcsr-of-set-rcx-high (equal (mxcsr (set-rcx-high val x86)) (mxcsr x86)) :hints (("Goal" :in-theory (enable mxcsr set-rcx-high))))
(defthm mxcsr-of-set-rdx-high (equal (mxcsr (set-rdx-high val x86)) (mxcsr x86)) :hints (("Goal" :in-theory (enable mxcsr set-rdx-high))))
;; (defthm mxcsr-of-set-rsi-high (equal (mxcsr (set-rsi-high val x86)) (mxcsr x86)) :hints (("Goal" :in-theory (enable mxcsr set-rsi-high))))
;; (defthm mxcsr-of-set-rdi-high (equal (mxcsr (set-rdi-high val x86)) (mxcsr x86)) :hints (("Goal" :in-theory (enable mxcsr set-rdi-high))))
(defthm mxcsr-of-set-rsp-high (equal (mxcsr (set-rsp-high val x86)) (mxcsr x86)) :hints (("Goal" :in-theory (enable mxcsr set-rsp-high))))
(defthm mxcsr-of-set-rbp-high (equal (mxcsr (set-rbp-high val x86)) (mxcsr x86)) :hints (("Goal" :in-theory (enable mxcsr set-rbp-high))))

(defthm undef-of-write-byte-to-segment
  (equal (undef (write-byte-to-segment eff-addr seg-reg val x86))
         (undef x86))
  :hints (("Goal" :in-theory (enable write-byte-to-segment))))

(defthm undef-of-write-to-segment
  (equal (undef (write-to-segment n eff-addr seg-reg val x86))
         (undef x86))
  :hints (("Goal" :in-theory (enable write-to-segment))))

(defthm mxcsr-of-write-byte-to-segment
  (equal (mxcsr (write-byte-to-segment eff-addr seg-reg val x86))
         (mxcsr x86))
  :hints (("Goal" :in-theory (enable write-byte-to-segment))))

(defthm mxcsr-of-write-to-segment
  (equal (mxcsr (write-to-segment n eff-addr seg-reg val x86))
         (mxcsr x86))
  :hints (("Goal" :in-theory (enable write-to-segment))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;(defthm ms-of-set-reg-high (equal (ms (set-reg-high reg val x86)) (ms x86)) :hints (("Goal" :in-theory (enable ms set-reg-high))))
(defthm ms-of-set-eip (equal (ms (set-eip val x86)) (ms x86)) :hints (("Goal" :in-theory (enable ms set-eip))))
(defthm ms-of-set-eax (equal (ms (set-eax val x86)) (ms x86)) :hints (("Goal" :in-theory (enable ms set-eax))))
(defthm ms-of-set-ebx (equal (ms (set-ebx val x86)) (ms x86)) :hints (("Goal" :in-theory (enable ms set-ebx))))
(defthm ms-of-set-ecx (equal (ms (set-ecx val x86)) (ms x86)) :hints (("Goal" :in-theory (enable ms set-ecx))))
(defthm ms-of-set-edx (equal (ms (set-edx val x86)) (ms x86)) :hints (("Goal" :in-theory (enable ms set-edx))))
;; (defthm ms-of-set-esi (equal (ms (set-esi val x86)) (ms x86)) :hints (("Goal" :in-theory (enable ms set-esi))))
;; (defthm ms-of-set-edi (equal (ms (set-edi val x86)) (ms x86)) :hints (("Goal" :in-theory (enable ms set-edi))))
(defthm ms-of-set-esp (equal (ms (set-esp val x86)) (ms x86)) :hints (("Goal" :in-theory (enable ms set-esp))))
(defthm ms-of-set-ebp (equal (ms (set-ebp val x86)) (ms x86)) :hints (("Goal" :in-theory (enable ms set-ebp))))

;(defthm ms-of-set-rip-high (equal (ms (set-rip-high val x86)) (ms x86)) :hints (("Goal" :in-theory (enable ms set-rip-high))))
(defthm ms-of-set-rax-high (equal (ms (set-rax-high val x86)) (ms x86)) :hints (("Goal" :in-theory (enable ms set-rax-high))))
(defthm ms-of-set-rbx-high (equal (ms (set-rbx-high val x86)) (ms x86)) :hints (("Goal" :in-theory (enable ms set-rbx-high))))
(defthm ms-of-set-rcx-high (equal (ms (set-rcx-high val x86)) (ms x86)) :hints (("Goal" :in-theory (enable ms set-rcx-high))))
(defthm ms-of-set-rdx-high (equal (ms (set-rdx-high val x86)) (ms x86)) :hints (("Goal" :in-theory (enable ms set-rdx-high))))
;; (defthm ms-of-set-rsi-high (equal (ms (set-rsi-high val x86)) (ms x86)) :hints (("Goal" :in-theory (enable ms set-rsi-high))))
;; (defthm ms-of-set-rdi-high (equal (ms (set-rdi-high val x86)) (ms x86)) :hints (("Goal" :in-theory (enable ms set-rdi-high))))
(defthm ms-of-set-rsp-high (equal (ms (set-rsp-high val x86)) (ms x86)) :hints (("Goal" :in-theory (enable ms set-rsp-high))))
(defthm ms-of-set-rbp-high (equal (ms (set-rbp-high val x86)) (ms x86)) :hints (("Goal" :in-theory (enable ms set-rbp-high))))

(defthm ms-of-write-byte-to-segment (equal (ms (write-byte-to-segment eff-addr seg-reg val x86)) (ms x86)) :hints (("Goal" :in-theory (enable write-byte-to-segment))))
(defthm ms-of-write-to-segment (equal (ms (write-to-segment n eff-addr seg-reg val x86)) (ms x86)) :hints (("Goal" :in-theory (enable write-to-segment))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;(defthm fault-of-set-reg-high (equal (fault (set-reg-high reg val x86)) (fault x86)) :hints (("Goal" :in-theory (enable fault set-reg-high))))
(defthm fault-of-set-eip (equal (fault (set-eip val x86)) (fault x86)) :hints (("Goal" :in-theory (enable fault set-eip))))
(defthm fault-of-set-eax (equal (fault (set-eax val x86)) (fault x86)) :hints (("Goal" :in-theory (enable fault set-eax))))
(defthm fault-of-set-ebx (equal (fault (set-ebx val x86)) (fault x86)) :hints (("Goal" :in-theory (enable fault set-ebx))))
(defthm fault-of-set-ecx (equal (fault (set-ecx val x86)) (fault x86)) :hints (("Goal" :in-theory (enable fault set-ecx))))
(defthm fault-of-set-edx (equal (fault (set-edx val x86)) (fault x86)) :hints (("Goal" :in-theory (enable fault set-edx))))
;; (defthm fault-of-set-esi (equal (fault (set-esi val x86)) (fault x86)) :hints (("Goal" :in-theory (enable fault set-esi))))
;; (defthm fault-of-set-edi (equal (fault (set-edi val x86)) (fault x86)) :hints (("Goal" :in-theory (enable fault set-edi))))
(defthm fault-of-set-esp (equal (fault (set-esp val x86)) (fault x86)) :hints (("Goal" :in-theory (enable fault set-esp))))
(defthm fault-of-set-ebp (equal (fault (set-ebp val x86)) (fault x86)) :hints (("Goal" :in-theory (enable fault set-ebp))))

;(defthm fault-of-set-rip-high (equal (fault (set-rip-high val x86)) (fault x86)) :hints (("Goal" :in-theory (enable fault set-rip-high))))
(defthm fault-of-set-rax-high (equal (fault (set-rax-high val x86)) (fault x86)) :hints (("Goal" :in-theory (enable fault set-rax-high))))
(defthm fault-of-set-rbx-high (equal (fault (set-rbx-high val x86)) (fault x86)) :hints (("Goal" :in-theory (enable fault set-rbx-high))))
(defthm fault-of-set-rcx-high (equal (fault (set-rcx-high val x86)) (fault x86)) :hints (("Goal" :in-theory (enable fault set-rcx-high))))
(defthm fault-of-set-rdx-high (equal (fault (set-rdx-high val x86)) (fault x86)) :hints (("Goal" :in-theory (enable fault set-rdx-high))))
;; (defthm fault-of-set-rsi-high (equal (fault (set-rsi-high val x86)) (fault x86)) :hints (("Goal" :in-theory (enable fault set-rsi-high))))
;; (defthm fault-of-set-rdi-high (equal (fault (set-rdi-high val x86)) (fault x86)) :hints (("Goal" :in-theory (enable fault set-rdi-high))))
(defthm fault-of-set-rsp-high (equal (fault (set-rsp-high val x86)) (fault x86)) :hints (("Goal" :in-theory (enable fault set-rsp-high))))
(defthm fault-of-set-rbp-high (equal (fault (set-rbp-high val x86)) (fault x86)) :hints (("Goal" :in-theory (enable fault set-rbp-high))))

(defthm fault-of-write-byte-to-segment (equal (fault (write-byte-to-segment eff-addr seg-reg val x86)) (fault x86)) :hints (("Goal" :in-theory (enable write-byte-to-segment))))
(defthm fault-of-write-to-segment (equal (fault (write-to-segment n eff-addr seg-reg val x86)) (fault x86)) :hints (("Goal" :in-theory (enable write-to-segment))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm program-at-of-set-eip
  (equal (program-at prog-addr bytes (set-eip eip x86))
         (program-at prog-addr bytes x86))
  :hints (("Goal" :in-theory (enable set-eip program-at))))

(defthm program-at-of-set-eax (equal (program-at addr bytes (set-eax val x86)) (program-at addr bytes x86)) :hints (("Goal" :in-theory (enable program-at set-eax))))
(defthm program-at-of-set-ebx (equal (program-at addr bytes (set-ebx val x86)) (program-at addr bytes x86)) :hints (("Goal" :in-theory (enable program-at set-ebx))))
(defthm program-at-of-set-ecx (equal (program-at addr bytes (set-ecx val x86)) (program-at addr bytes x86)) :hints (("Goal" :in-theory (enable program-at set-ecx))))
(defthm program-at-of-set-edx (equal (program-at addr bytes (set-edx val x86)) (program-at addr bytes x86)) :hints (("Goal" :in-theory (enable program-at set-edx))))
;; (defthm program-at-of-set-esi (equal (program-at addr bytes (set-esi val x86)) (program-at addr bytes x86)) :hints (("Goal" :in-theory (enable program-at set-esi))))
;; (defthm program-at-of-set-edi (equal (program-at addr bytes (set-edi val x86)) (program-at addr bytes x86)) :hints (("Goal" :in-theory (enable program-at set-edi))))
(defthm program-at-of-set-esp (equal (program-at addr bytes (set-esp val x86)) (program-at addr bytes x86)) :hints (("Goal" :in-theory (enable program-at set-esp))))
(defthm program-at-of-set-ebp (equal (program-at addr bytes (set-ebp val x86)) (program-at addr bytes x86)) :hints (("Goal" :in-theory (enable program-at set-ebp))))

(defthm program-at-of-set-rax-high (equal (program-at addr bytes (set-rax-high val x86)) (program-at addr bytes x86)) :hints (("Goal" :in-theory (enable program-at set-rax-high))))
(defthm program-at-of-set-rbx-high (equal (program-at addr bytes (set-rbx-high val x86)) (program-at addr bytes x86)) :hints (("Goal" :in-theory (enable program-at set-rbx-high))))
(defthm program-at-of-set-rcx-high (equal (program-at addr bytes (set-rcx-high val x86)) (program-at addr bytes x86)) :hints (("Goal" :in-theory (enable program-at set-rcx-high))))
(defthm program-at-of-set-rdx-high (equal (program-at addr bytes (set-rdx-high val x86)) (program-at addr bytes x86)) :hints (("Goal" :in-theory (enable program-at set-rdx-high))))
;; (defthm program-at-of-set-rsi-high (equal (program-at addr bytes (set-rsi-high val x86)) (program-at addr bytes x86)) :hints (("Goal" :in-theory (enable program-at set-rsi-high))))
;; (defthm program-at-of-set-rdi-high (equal (program-at addr bytes (set-rdi-high val x86)) (program-at addr bytes x86)) :hints (("Goal" :in-theory (enable program-at set-rdi-high))))
(defthm program-at-of-set-rsp-high (equal (program-at addr bytes (set-rsp-high val x86)) (program-at addr bytes x86)) :hints (("Goal" :in-theory (enable program-at set-rsp-high))))
(defthm program-at-of-set-rbp-high (equal (program-at addr bytes (set-rbp-high val x86)) (program-at addr bytes x86)) :hints (("Goal" :in-theory (enable program-at set-rbp-high))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
