; "Write over write" rules for our x86-64 state writers
;
; Copyright (C) 2016-2025 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

(include-book "register-readers-and-writers64")
(include-book "flags")
(include-book "read-and-write")
(include-book "read-bytes-and-write-bytes")
(include-book "readers-and-writers")
(include-book "read-over-write-rules64") ; to support mixed rules like read-of-write-of-set-flag

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm write-byte-of-xw-irrel
  (implies (not (equal :mem fld))
           (equal (write-byte addr byte (xw fld index val x86))
                  (xw fld index val (write-byte addr byte x86))))
  :hints (("Goal" :in-theory (enable write-byte !memi))))

(defthm set-flag-of-write-byte
  (equal (set-flag flg val (write-byte addr byte x86))
         (write-byte addr byte (set-flag flg val x86)))
  :hints (("Goal" :in-theory (enable set-flag wb write-byte !memi))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm write-of-xw-irrel
  (implies (not (equal :mem fld))
           (equal (write n addr value (xw fld index val x86))
                  (xw fld index val (write n addr value x86))))
  :hints (("Goal" :in-theory (enable write))))

(defthm !rflags-of-write
  (equal (!rflags rflags (write n addr val x86))
         (write n addr val (!rflags rflags x86)))
  :hints (("Goal" :in-theory (enable !rflags))))

(defthmd write-of-!rflags
  (equal (write n addr val (!rflags rflags x86))
         (!rflags rflags (write n addr val x86))))

(theory-invariant (incompatible (:rewrite !rflags-of-write) (:rewrite write-of-!rflags)))

(defthm set-flag-of-write
  (equal (set-flag flg val (write n addr value x86))
         (write n addr value (set-flag flg val x86)))
  :hints (("Goal" :in-theory (enable set-flag wb write))))

(defthmd write-of-set-flag
  (equal (write n addr val1 (set-flag flg val2 x86))
         (set-flag flg val2 (write n addr val1 x86)))
  :hints (("Goal" :in-theory (enable set-flag wb write))))

(theory-invariant (incompatible (:rewrite write-of-set-flag) (:rewrite set-flag-of-write)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm write-bytes-of-xw-irrel
  (implies (not (equal :mem fld))
           (equal (write-bytes addr values (xw fld index val x86))
                  (xw fld index val (write-bytes addr values x86))))
  :hints (("Goal" :in-theory (enable write-bytes))))

(defthm set-flag-of-write-bytes
  (equal (set-flag flg val (write-bytes addr values x86))
         (write-bytes addr values (set-flag flg val x86)))
  :hints (("Goal" :in-theory (enable set-flag wb write-bytes))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; These push write-byte inward:
(defthm write-byte-of-set-rip (equal (write-byte base-addr byte (set-rip rip x86)) (set-rip rip (write-byte base-addr byte x86))) :hints (("Goal" :in-theory (enable write-byte))))
(defthm write-byte-of-set-rax (equal (write-byte base-addr byte (set-rax rax x86)) (set-rax rax (write-byte base-addr byte x86))) :hints (("Goal" :in-theory (enable write-byte set-rax))))
(defthm write-byte-of-set-rbx (equal (write-byte base-addr byte (set-rbx rbx x86)) (set-rbx rbx (write-byte base-addr byte x86))) :hints (("Goal" :in-theory (enable write-byte set-rbx))))
(defthm write-byte-of-set-rcx (equal (write-byte base-addr byte (set-rcx rcx x86)) (set-rcx rcx (write-byte base-addr byte x86))) :hints (("Goal" :in-theory (enable write-byte set-rcx))))
(defthm write-byte-of-set-rdx (equal (write-byte base-addr byte (set-rdx rdx x86)) (set-rdx rdx (write-byte base-addr byte x86))) :hints (("Goal" :in-theory (enable write-byte set-rdx))))
(defthm write-byte-of-set-rsi (equal (write-byte base-addr byte (set-rsi rsi x86)) (set-rsi rsi (write-byte base-addr byte x86))) :hints (("Goal" :in-theory (enable write-byte set-rsi))))
(defthm write-byte-of-set-rdi (equal (write-byte base-addr byte (set-rdi rdi x86)) (set-rdi rdi (write-byte base-addr byte x86))) :hints (("Goal" :in-theory (enable write-byte set-rdi))))
(defthm write-byte-of-set-r8 (equal (write-byte base-addr byte (set-r8 r8 x86)) (set-r8 r8 (write-byte base-addr byte x86))) :hints (("Goal" :in-theory (enable write-byte set-r8))))
(defthm write-byte-of-set-r9 (equal (write-byte base-addr byte (set-r9 r9 x86)) (set-r9 r9 (write-byte base-addr byte x86))) :hints (("Goal" :in-theory (enable write-byte set-r9))))
(defthm write-byte-of-set-r10 (equal (write-byte base-addr byte (set-r10 r10 x86)) (set-r10 r10 (write-byte base-addr byte x86))) :hints (("Goal" :in-theory (enable write-byte set-r10))))
(defthm write-byte-of-set-r11 (equal (write-byte base-addr byte (set-r11 r11 x86)) (set-r11 r11 (write-byte base-addr byte x86))) :hints (("Goal" :in-theory (enable write-byte set-r11))))
(defthm write-byte-of-set-r12 (equal (write-byte base-addr byte (set-r12 r12 x86)) (set-r12 r12 (write-byte base-addr byte x86))) :hints (("Goal" :in-theory (enable write-byte set-r12))))
(defthm write-byte-of-set-r13 (equal (write-byte base-addr byte (set-r13 r13 x86)) (set-r13 r13 (write-byte base-addr byte x86))) :hints (("Goal" :in-theory (enable write-byte set-r13))))
(defthm write-byte-of-set-r14 (equal (write-byte base-addr byte (set-r14 r14 x86)) (set-r14 r14 (write-byte base-addr byte x86))) :hints (("Goal" :in-theory (enable write-byte set-r14))))
(defthm write-byte-of-set-r15 (equal (write-byte base-addr byte (set-r15 r15 x86)) (set-r15 r15 (write-byte base-addr byte x86))) :hints (("Goal" :in-theory (enable write-byte set-r15))))
(defthm write-byte-of-set-rsp (equal (write-byte base-addr byte (set-rsp rsp x86)) (set-rsp rsp (write-byte base-addr byte x86))) :hints (("Goal" :in-theory (enable write-byte set-rsp))))
(defthm write-byte-of-set-rbp (equal (write-byte base-addr byte (set-rbp rbp x86)) (set-rbp rbp (write-byte base-addr byte x86))) :hints (("Goal" :in-theory (enable write-byte set-rbp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; These push write inward:
(defthm write-of-set-rip (equal (write n base-addr val (set-rip rip x86)) (set-rip rip (write n base-addr val x86))) :hints (("Goal" :in-theory (enable write))))
(defthm write-of-set-rax (equal (write n base-addr val (set-rax rax x86)) (set-rax rax (write n base-addr val x86))) :hints (("Goal" :in-theory (enable write set-rax))))
(defthm write-of-set-rbx (equal (write n base-addr val (set-rbx rbx x86)) (set-rbx rbx (write n base-addr val x86))) :hints (("Goal" :in-theory (enable write set-rbx))))
(defthm write-of-set-rcx (equal (write n base-addr val (set-rcx rcx x86)) (set-rcx rcx (write n base-addr val x86))) :hints (("Goal" :in-theory (enable write set-rcx))))
(defthm write-of-set-rdx (equal (write n base-addr val (set-rdx rdx x86)) (set-rdx rdx (write n base-addr val x86))) :hints (("Goal" :in-theory (enable write set-rdx))))
(defthm write-of-set-rsi (equal (write n base-addr val (set-rsi rsi x86)) (set-rsi rsi (write n base-addr val x86))) :hints (("Goal" :in-theory (enable write set-rsi))))
(defthm write-of-set-rdi (equal (write n base-addr val (set-rdi rdi x86)) (set-rdi rdi (write n base-addr val x86))) :hints (("Goal" :in-theory (enable write set-rdi))))
(defthm write-of-set-r8 (equal (write n base-addr byte (set-r8 r8 x86)) (set-r8 r8 (write n base-addr byte x86))) :hints (("Goal" :in-theory (enable write set-r8))))
(defthm write-of-set-r9 (equal (write n base-addr byte (set-r9 r9 x86)) (set-r9 r9 (write n base-addr byte x86))) :hints (("Goal" :in-theory (enable write set-r9))))
(defthm write-of-set-r10 (equal (write n base-addr byte (set-r10 r10 x86)) (set-r10 r10 (write n base-addr byte x86))) :hints (("Goal" :in-theory (enable write set-r10))))
(defthm write-of-set-r11 (equal (write n base-addr byte (set-r11 r11 x86)) (set-r11 r11 (write n base-addr byte x86))) :hints (("Goal" :in-theory (enable write set-r11))))
(defthm write-of-set-r12 (equal (write n base-addr byte (set-r12 r12 x86)) (set-r12 r12 (write n base-addr byte x86))) :hints (("Goal" :in-theory (enable write set-r12))))
(defthm write-of-set-r13 (equal (write n base-addr byte (set-r13 r13 x86)) (set-r13 r13 (write n base-addr byte x86))) :hints (("Goal" :in-theory (enable write set-r13))))
(defthm write-of-set-r14 (equal (write n base-addr byte (set-r14 r14 x86)) (set-r14 r14 (write n base-addr byte x86))) :hints (("Goal" :in-theory (enable write set-r14))))
(defthm write-of-set-r15 (equal (write n base-addr byte (set-r15 r15 x86)) (set-r15 r15 (write n base-addr byte x86))) :hints (("Goal" :in-theory (enable write set-r15))))
(defthm write-of-set-rsp (equal (write n base-addr val (set-rsp rsp x86)) (set-rsp rsp (write n base-addr val x86))) :hints (("Goal" :in-theory (enable write set-rsp))))
(defthm write-of-set-rbp (equal (write n base-addr val (set-rbp rbp x86)) (set-rbp rbp (write n base-addr val x86))) :hints (("Goal" :in-theory (enable write set-rbp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; These push set-flag inward:
(defthm set-flag-of-set-rip (equal (set-flag flag fval (set-rip rip x86)) (set-rip rip (set-flag flag fval x86))) :hints (("Goal" :in-theory (enable set-flag))))
(defthm set-flag-of-set-rax (equal (set-flag flag fval (set-rax rax x86)) (set-rax rax (set-flag flag fval x86))) :hints (("Goal" :in-theory (enable set-flag))))
(defthm set-flag-of-set-rbx (equal (set-flag flag fval (set-rbx rbx x86)) (set-rbx rbx (set-flag flag fval x86))) :hints (("Goal" :in-theory (enable set-flag))))
(defthm set-flag-of-set-rcx (equal (set-flag flag fval (set-rcx rcx x86)) (set-rcx rcx (set-flag flag fval x86))) :hints (("Goal" :in-theory (enable set-flag))))
(defthm set-flag-of-set-rdx (equal (set-flag flag fval (set-rdx rdx x86)) (set-rdx rdx (set-flag flag fval x86))) :hints (("Goal" :in-theory (enable set-flag))))
(defthm set-flag-of-set-rsi (equal (set-flag flag fval (set-rsi rsi x86)) (set-rsi rsi (set-flag flag fval x86))) :hints (("Goal" :in-theory (enable set-flag))))
(defthm set-flag-of-set-rdi (equal (set-flag flag fval (set-rdi rdi x86)) (set-rdi rdi (set-flag flag fval x86))) :hints (("Goal" :in-theory (enable set-flag))))
(defthm set-flag-of-set-r8 (equal (set-flag flag fval (set-r8 r8 x86)) (set-r8 r8 (set-flag flag fval x86))) :hints (("Goal" :in-theory (enable set-flag set-r8))))
(defthm set-flag-of-set-r9 (equal (set-flag flag fval (set-r9 r9 x86)) (set-r9 r9 (set-flag flag fval x86))) :hints (("Goal" :in-theory (enable set-flag set-r9))))
(defthm set-flag-of-set-r10 (equal (set-flag flag fval (set-r10 r10 x86)) (set-r10 r10 (set-flag flag fval x86))) :hints (("Goal" :in-theory (enable set-flag set-r10))))
(defthm set-flag-of-set-r11 (equal (set-flag flag fval (set-r11 r11 x86)) (set-r11 r11 (set-flag flag fval x86))) :hints (("Goal" :in-theory (enable set-flag set-r11))))
(defthm set-flag-of-set-r12 (equal (set-flag flag fval (set-r12 r12 x86)) (set-r12 r12 (set-flag flag fval x86))) :hints (("Goal" :in-theory (enable set-flag set-r12))))
(defthm set-flag-of-set-r13 (equal (set-flag flag fval (set-r13 r13 x86)) (set-r13 r13 (set-flag flag fval x86))) :hints (("Goal" :in-theory (enable set-flag set-r13))))
(defthm set-flag-of-set-r14 (equal (set-flag flag fval (set-r14 r14 x86)) (set-r14 r14 (set-flag flag fval x86))) :hints (("Goal" :in-theory (enable set-flag set-r14))))
(defthm set-flag-of-set-r15 (equal (set-flag flag fval (set-r15 r15 x86)) (set-r15 r15 (set-flag flag fval x86))) :hints (("Goal" :in-theory (enable set-flag set-r15))))
(defthm set-flag-of-set-rsp (equal (set-flag flag fval (set-rsp rsp x86)) (set-rsp rsp (set-flag flag fval x86))) :hints (("Goal" :in-theory (enable set-flag))))
(defthm set-flag-of-set-rbp (equal (set-flag flag fval (set-rbp rbp x86)) (set-rbp rbp (set-flag flag fval x86))) :hints (("Goal" :in-theory (enable set-flag))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; These pull set-rip outward:
(local (in-theory (disable xw-becomes-set-rip)))
(defthm set-rax-of-set-rip (equal (set-rax rax (set-rip rip x86)) (set-rip rip (set-rax rax x86))) :hints (("Goal" :in-theory (enable set-rip))))
(defthm set-rbx-of-set-rip (equal (set-rbx rbx (set-rip rip x86)) (set-rip rip (set-rbx rbx x86))) :hints (("Goal" :in-theory (enable set-rip))))
(defthm set-rcx-of-set-rip (equal (set-rcx rcx (set-rip rip x86)) (set-rip rip (set-rcx rcx x86))) :hints (("Goal" :in-theory (enable set-rip))))
(defthm set-rdx-of-set-rip (equal (set-rdx rdx (set-rip rip x86)) (set-rip rip (set-rdx rdx x86))) :hints (("Goal" :in-theory (enable set-rip))))
(defthm set-rsi-of-set-rip (equal (set-rsi rsi (set-rip rip x86)) (set-rip rip (set-rsi rsi x86))) :hints (("Goal" :in-theory (enable set-rip))))
(defthm set-rdi-of-set-rip (equal (set-rdi rdi (set-rip rip x86)) (set-rip rip (set-rdi rdi x86))) :hints (("Goal" :in-theory (enable set-rip))))
(defthm set-r8-of-set-rip (equal (set-r8 r8 (set-rip rip x86)) (set-rip rip (set-r8 r8 x86))) :hints (("Goal" :in-theory (enable set-rip set-r8))))
(defthm set-r9-of-set-rip (equal (set-r9 r9 (set-rip rip x86)) (set-rip rip (set-r9 r9 x86))) :hints (("Goal" :in-theory (enable set-rip set-r9))))
(defthm set-r10-of-set-rip (equal (set-r10 r10 (set-rip rip x86)) (set-rip rip (set-r10 r10 x86))) :hints (("Goal" :in-theory (enable set-rip set-r10))))
(defthm set-r11-of-set-rip (equal (set-r11 r11 (set-rip rip x86)) (set-rip rip (set-r11 r11 x86))) :hints (("Goal" :in-theory (enable set-rip set-r11))))
(defthm set-r12-of-set-rip (equal (set-r12 r12 (set-rip rip x86)) (set-rip rip (set-r12 r12 x86))) :hints (("Goal" :in-theory (enable set-rip set-r12))))
(defthm set-r13-of-set-rip (equal (set-r13 r13 (set-rip rip x86)) (set-rip rip (set-r13 r13 x86))) :hints (("Goal" :in-theory (enable set-rip set-r13))))
(defthm set-r14-of-set-rip (equal (set-r14 r14 (set-rip rip x86)) (set-rip rip (set-r14 r14 x86))) :hints (("Goal" :in-theory (enable set-rip set-r14))))
(defthm set-r15-of-set-rip (equal (set-r15 r15 (set-rip rip x86)) (set-rip rip (set-r15 r15 x86))) :hints (("Goal" :in-theory (enable set-rip set-r15))))
(defthm set-rsp-of-set-rip (equal (set-rsp rsp (set-rip rip x86)) (set-rip rip (set-rsp rsp x86))) :hints (("Goal" :in-theory (enable set-rip))))
(defthm set-rbp-of-set-rip (equal (set-rbp rbp (set-rip rip x86)) (set-rip rip (set-rbp rbp x86))) :hints (("Goal" :in-theory (enable set-rip))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; These push set-undef inward:
(defthm set-undef-of-set-rip (equal (set-undef undef (set-rip rip x86)) (set-rip rip (set-undef undef x86))) :hints (("Goal" :in-theory (enable set-undef))))
(defthm set-undef-of-set-rax (equal (set-undef undef (set-rax rax x86)) (set-rax rax (set-undef undef x86))) :hints (("Goal" :in-theory (enable set-undef set-rax))))
(defthm set-undef-of-set-rbx (equal (set-undef undef (set-rbx rbx x86)) (set-rbx rbx (set-undef undef x86))) :hints (("Goal" :in-theory (enable set-undef set-rbx))))
(defthm set-undef-of-set-rcx (equal (set-undef undef (set-rcx rcx x86)) (set-rcx rcx (set-undef undef x86))) :hints (("Goal" :in-theory (enable set-undef set-rcx))))
(defthm set-undef-of-set-rdx (equal (set-undef undef (set-rdx rdx x86)) (set-rdx rdx (set-undef undef x86))) :hints (("Goal" :in-theory (enable set-undef set-rdx))))
(defthm set-undef-of-set-rsi (equal (set-undef undef (set-rsi rsi x86)) (set-rsi rsi (set-undef undef x86))) :hints (("Goal" :in-theory (enable set-undef set-rsi))))
(defthm set-undef-of-set-rdi (equal (set-undef undef (set-rdi rdi x86)) (set-rdi rdi (set-undef undef x86))) :hints (("Goal" :in-theory (enable set-undef set-rdi))))
(defthm set-undef-of-set-r8 (equal (set-undef undef (set-r8 r8 x86)) (set-r8 r8 (set-undef undef x86))) :hints (("Goal" :in-theory (enable set-undef set-r8))))
(defthm set-undef-of-set-r9 (equal (set-undef undef (set-r9 r9 x86)) (set-r9 r9 (set-undef undef x86))) :hints (("Goal" :in-theory (enable set-undef set-r9))))
(defthm set-undef-of-set-r10 (equal (set-undef undef (set-r10 r10 x86)) (set-r10 r10 (set-undef undef x86))) :hints (("Goal" :in-theory (enable set-undef set-r10))))
(defthm set-undef-of-set-r11 (equal (set-undef undef (set-r11 r11 x86)) (set-r11 r11 (set-undef undef x86))) :hints (("Goal" :in-theory (enable set-undef set-r11))))
(defthm set-undef-of-set-r12 (equal (set-undef undef (set-r12 r12 x86)) (set-r12 r12 (set-undef undef x86))) :hints (("Goal" :in-theory (enable set-undef set-r12))))
(defthm set-undef-of-set-r13 (equal (set-undef undef (set-r13 r13 x86)) (set-r13 r13 (set-undef undef x86))) :hints (("Goal" :in-theory (enable set-undef set-r13))))
(defthm set-undef-of-set-r14 (equal (set-undef undef (set-r14 r14 x86)) (set-r14 r14 (set-undef undef x86))) :hints (("Goal" :in-theory (enable set-undef set-r14))))
(defthm set-undef-of-set-r15 (equal (set-undef undef (set-r15 r15 x86)) (set-r15 r15 (set-undef undef x86))) :hints (("Goal" :in-theory (enable set-undef set-r15))))
(defthm set-undef-of-set-rsp (equal (set-undef undef (set-rsp rsp x86)) (set-rsp rsp (set-undef undef x86))) :hints (("Goal" :in-theory (enable set-undef set-rsp))))
(defthm set-undef-of-set-rbp (equal (set-undef undef (set-rbp rbp x86)) (set-rbp rbp (set-undef undef x86))) :hints (("Goal" :in-theory (enable set-undef set-rbp))))

(defthm set-undef-of-write-byte (equal (set-undef undef (write-byte base-addr byte x86)) (write-byte base-addr byte (set-undef undef x86))) :hints (("Goal" :in-theory (enable write-byte set-undef))))

(defthm set-undef-of-write (equal (set-undef undef (write n base-addr val x86)) (write n base-addr val (set-undef undef x86))) :hints (("Goal" :in-theory (enable write set-undef))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; These push set-mxcsr inward:
(defthm set-mxcsr-of-set-rip (equal (set-mxcsr mxcsr (set-rip rip x86)) (set-rip rip (set-mxcsr mxcsr x86))) :hints (("Goal" :in-theory (enable set-mxcsr))))
(defthm set-mxcsr-of-set-rax (equal (set-mxcsr mxcsr (set-rax rax x86)) (set-rax rax (set-mxcsr mxcsr x86))) :hints (("Goal" :in-theory (enable set-mxcsr set-rax))))
(defthm set-mxcsr-of-set-rbx (equal (set-mxcsr mxcsr (set-rbx rbx x86)) (set-rbx rbx (set-mxcsr mxcsr x86))) :hints (("Goal" :in-theory (enable set-mxcsr set-rbx))))
(defthm set-mxcsr-of-set-rcx (equal (set-mxcsr mxcsr (set-rcx rcx x86)) (set-rcx rcx (set-mxcsr mxcsr x86))) :hints (("Goal" :in-theory (enable set-mxcsr set-rcx))))
(defthm set-mxcsr-of-set-rdx (equal (set-mxcsr mxcsr (set-rdx rdx x86)) (set-rdx rdx (set-mxcsr mxcsr x86))) :hints (("Goal" :in-theory (enable set-mxcsr set-rdx))))
(defthm set-mxcsr-of-set-rsi (equal (set-mxcsr mxcsr (set-rsi rsi x86)) (set-rsi rsi (set-mxcsr mxcsr x86))) :hints (("Goal" :in-theory (enable set-mxcsr set-rsi))))
(defthm set-mxcsr-of-set-rdi (equal (set-mxcsr mxcsr (set-rdi rdi x86)) (set-rdi rdi (set-mxcsr mxcsr x86))) :hints (("Goal" :in-theory (enable set-mxcsr set-rdi))))
(defthm set-mxcsr-of-set-r8 (equal (set-mxcsr mxcsr (set-r8 r8 x86)) (set-r8 r8 (set-mxcsr mxcsr x86))) :hints (("Goal" :in-theory (enable set-mxcsr set-r8))))
(defthm set-mxcsr-of-set-r9 (equal (set-mxcsr mxcsr (set-r9 r9 x86)) (set-r9 r9 (set-mxcsr mxcsr x86))) :hints (("Goal" :in-theory (enable set-mxcsr set-r9))))
(defthm set-mxcsr-of-set-r10 (equal (set-mxcsr mxcsr (set-r10 r10 x86)) (set-r10 r10 (set-mxcsr mxcsr x86))) :hints (("Goal" :in-theory (enable set-mxcsr set-r10))))
(defthm set-mxcsr-of-set-r11 (equal (set-mxcsr mxcsr (set-r11 r11 x86)) (set-r11 r11 (set-mxcsr mxcsr x86))) :hints (("Goal" :in-theory (enable set-mxcsr set-r11))))
(defthm set-mxcsr-of-set-r12 (equal (set-mxcsr mxcsr (set-r12 r12 x86)) (set-r12 r12 (set-mxcsr mxcsr x86))) :hints (("Goal" :in-theory (enable set-mxcsr set-r12))))
(defthm set-mxcsr-of-set-r13 (equal (set-mxcsr mxcsr (set-r13 r13 x86)) (set-r13 r13 (set-mxcsr mxcsr x86))) :hints (("Goal" :in-theory (enable set-mxcsr set-r13))))
(defthm set-mxcsr-of-set-r14 (equal (set-mxcsr mxcsr (set-r14 r14 x86)) (set-r14 r14 (set-mxcsr mxcsr x86))) :hints (("Goal" :in-theory (enable set-mxcsr set-r14))))
(defthm set-mxcsr-of-set-r15 (equal (set-mxcsr mxcsr (set-r15 r15 x86)) (set-r15 r15 (set-mxcsr mxcsr x86))) :hints (("Goal" :in-theory (enable set-mxcsr set-r15))))
(defthm set-mxcsr-of-set-rsp (equal (set-mxcsr mxcsr (set-rsp rsp x86)) (set-rsp rsp (set-mxcsr mxcsr x86))) :hints (("Goal" :in-theory (enable set-mxcsr set-rsp))))
(defthm set-mxcsr-of-set-rbp (equal (set-mxcsr mxcsr (set-rbp rbp x86)) (set-rbp rbp (set-mxcsr mxcsr x86))) :hints (("Goal" :in-theory (enable set-mxcsr set-rbp))))

(defthm set-mxcsr-of-write-byte (equal (set-mxcsr mxcsr (write-byte base-addr byte x86)) (write-byte base-addr byte (set-mxcsr mxcsr x86))) :hints (("Goal" :in-theory (enable write-byte set-mxcsr))))

(defthm set-mxcsr-of-write (equal (set-mxcsr mxcsr (write n base-addr val x86)) (write n base-addr val (set-mxcsr mxcsr x86))) :hints (("Goal" :in-theory (enable write set-mxcsr))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm !rflags-of-set-rip (equal (!rflags flags (set-rip rip x86)) (set-rip rip (!rflags flags x86))) :hints (("Goal" :in-theory (enable !rflags))))
(defthm !rflags-of-set-rax (equal (!rflags flags (set-rax rax x86)) (set-rax rax (!rflags flags x86))) :hints (("Goal" :in-theory (enable !rflags set-rax))))
(defthm !rflags-of-set-rbx (equal (!rflags flags (set-rbx rbx x86)) (set-rbx rbx (!rflags flags x86))) :hints (("Goal" :in-theory (enable !rflags set-rbx))))
(defthm !rflags-of-set-rcx (equal (!rflags flags (set-rcx rcx x86)) (set-rcx rcx (!rflags flags x86))) :hints (("Goal" :in-theory (enable !rflags set-rcx))))
(defthm !rflags-of-set-rdx (equal (!rflags flags (set-rdx rdx x86)) (set-rdx rdx (!rflags flags x86))) :hints (("Goal" :in-theory (enable !rflags set-rdx))))
(defthm !rflags-of-set-rdi (equal (!rflags flags (set-rdi rdi x86)) (set-rdi rdi (!rflags flags x86))) :hints (("Goal" :in-theory (enable !rflags set-rdi))))
(defthm !rflags-of-set-rsi (equal (!rflags flags (set-rsi rsi x86)) (set-rsi rsi (!rflags flags x86))) :hints (("Goal" :in-theory (enable !rflags set-rsi))))
(defthm !rflags-of-set-r8 (equal (!rflags flags (set-r8 r8 x86)) (set-r8 r8 (!rflags flags x86))) :hints (("Goal" :in-theory (enable !rflags set-r8))))
(defthm !rflags-of-set-r9 (equal (!rflags flags (set-r9 r9 x86)) (set-r9 r9 (!rflags flags x86))) :hints (("Goal" :in-theory (enable !rflags set-r9))))
(defthm !rflags-of-set-r10 (equal (!rflags flags (set-r10 r10 x86)) (set-r10 r10 (!rflags flags x86))) :hints (("Goal" :in-theory (enable !rflags set-r10))))
(defthm !rflags-of-set-r11 (equal (!rflags flags (set-r11 r11 x86)) (set-r11 r11 (!rflags flags x86))) :hints (("Goal" :in-theory (enable !rflags set-r11))))
(defthm !rflags-of-set-r12 (equal (!rflags flags (set-r12 r12 x86)) (set-r12 r12 (!rflags flags x86))) :hints (("Goal" :in-theory (enable !rflags set-r12))))
(defthm !rflags-of-set-r13 (equal (!rflags flags (set-r13 r13 x86)) (set-r13 r13 (!rflags flags x86))) :hints (("Goal" :in-theory (enable !rflags set-r13))))
(defthm !rflags-of-set-r14 (equal (!rflags flags (set-r14 r14 x86)) (set-r14 r14 (!rflags flags x86))) :hints (("Goal" :in-theory (enable !rflags set-r14))))
(defthm !rflags-of-set-r15 (equal (!rflags flags (set-r15 r15 x86)) (set-r15 r15 (!rflags flags x86))) :hints (("Goal" :in-theory (enable !rflags set-r15))))
(defthm !rflags-of-set-rsp (equal (!rflags flags (set-rsp rsp x86)) (set-rsp rsp (!rflags flags x86))) :hints (("Goal" :in-theory (enable !rflags set-rsp))))
(defthm !rflags-of-set-rbp (equal (!rflags flags (set-rbp rbp x86)) (set-rbp rbp (!rflags flags x86))) :hints (("Goal" :in-theory (enable !rflags set-rbp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; These just make the terms nicer (todo: just use the general scheme?)
(defthm read-of-write-of-set-flag
  (equal (read n addr (write n1 addr1 val1 (set-flag flag val x86)))
         (read n addr (write n1 addr1 val1 x86)))
  :hints (("Goal" :in-theory (e/d (write-of-set-flag) (set-flag-of-write)))))

(defthm read-of-write-of-write-of-set-flag
  (equal (read n addr (write n1 addr1 val1 (write n2 addr2 val2 (set-flag flag val x86))))
         (read n addr (write n1 addr1 val1 (write n2 addr2 val2 x86))))
  :hints (("Goal" :in-theory (e/d (write-of-set-flag) (set-flag-of-write)))))

(defthm read-of-write-of-write-of-write-of-set-flag
  (equal (read n addr (write n1 addr1 val1 (write n2 addr2 val2 (write n3 addr3 val3 (set-flag flag val x86)))))
         (read n addr (write n1 addr1 val1 (write n2 addr2 val2 (write n3 addr3 val3 x86)))))
  :hints (("Goal" :in-theory (e/d (write-of-set-flag) (set-flag-of-write)))))
