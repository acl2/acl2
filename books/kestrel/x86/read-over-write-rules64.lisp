; "Read over write" rules for our x86 state readers and writers
;
; Copyright (C) 2016-2025 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

(include-book "register-readers-and-writers64")
(include-book "projects/x86isa/machine/modes" :dir :system)
(include-book "flags")
(include-book "read-and-write")
(include-book "read-bytes-and-write-bytes")
(include-book "readers-and-writers")
(include-book "support") ;todo: remove (factor out non-32-bit read-over-write stuff like mv-nth-0-of-get-prefixes-of-xw-of-irrel)

;; TODO: Make sure we have the complete set of these rules

;; The readers are: rip, the 16 (other) register readers, get-flag, ctri, undef, read, (todo: read-byte?) (todo: rflags?), msri

;; The predicates are: x86p, alignment-checking-enabled-p, 64-bit-modep, app-view

;; The writers are: the 16 register writers, set-rip, set-flag, set-undef, write, write-byte, !rflags (todo: why?)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm read-byte-of-xw-irrel
  (implies (not (equal fld :mem))
           (equal (read-byte addr (xw fld index val x86))
                  (read-byte addr x86)))
  :hints (("Goal" :in-theory (enable read-byte))))

(defthm read-byte-of-set-flag
  (equal (read-byte addr (set-flag flag val x86))
         (read-byte addr x86))
  :hints (("Goal" :in-theory (enable read-byte))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm xr-of-write-byte-when-not-mem
  (implies (not (equal :mem fld))
           (equal (xr fld index (write-byte addr byte x86))
                  (xr fld index x86)))
  :hints (("Goal" :in-theory (enable write-byte))))

(defthm 64-bit-modep-of-write-byte
  (equal (64-bit-modep (write-byte addr byte x86))
         (64-bit-modep x86))
  :hints (("Goal" :in-theory (enable write-byte))))

(defthm app-view-of-write-byte
  (equal (app-view (write-byte addr byte x86))
         (app-view x86))
  :hints (("Goal" :in-theory (enable write-byte))))

(defthm alignment-checking-enabled-p-of-write-byte
  (equal (alignment-checking-enabled-p (write-byte addr byte x86))
         (alignment-checking-enabled-p x86))
  :hints (("Goal" :in-theory (enable write-byte))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm read-of-xw-irrel
  (implies (not (equal fld :mem))
           (equal (read n addr (xw fld index val x86))
                  (read n addr x86)))
  :hints (("Goal" :in-theory (enable read memi))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; todo: name -irrel
(defthm xr-of-write-when-not-mem
  (implies (not (equal :mem fld))
           (equal (xr fld index (write n addr val x86))
                  (xr fld index x86)))
  :hints (("Goal" :in-theory (enable write))))

(defthm 64-bit-modep-of-write
  (equal (64-bit-modep (write n addr val x86))
         (64-bit-modep x86))
  :hints (("Goal" :in-theory (enable write))))

(defthm app-view-of-write
  (equal (app-view (write n addr val x86))
         (app-view x86))
  :hints (("Goal" :in-theory (enable write))))

(defthm alignment-checking-enabled-p-of-write
  (equal (alignment-checking-enabled-p (write n addr val x86))
         (alignment-checking-enabled-p x86))
  :hints (("Goal" :in-theory (enable write))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm xr-of-write-bytes
  (implies (not (equal :mem fld))
           (equal (xr fld index (write-bytes addr vals x86))
                  (xr fld index x86)))
  :hints (("Goal" :in-theory (enable write-bytes))))

(defthm 64-bit-modep-of-write-bytes
  (equal (64-bit-modep (write-bytes addr vals x86))
         (64-bit-modep x86))
  :hints (("Goal" :in-theory (enable write-bytes))))

(defthm app-view-of-write-bytes
  (equal (app-view (write-bytes addr vals x86))
         (app-view x86))
  :hints (("Goal" :in-theory (enable write-bytes))))

(defthm alignment-checking-enabled-p-of-write-bytes
  (equal (alignment-checking-enabled-p (write-bytes addr vals x86))
         (alignment-checking-enabled-p x86))
  :hints (("Goal" :in-theory (enable write-bytes))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This section contains rules for the 17 register readers (including RIP)
;; applied after various writers, organized by writer.

;; This first one may be rarely needed, since set-rip is moved above set-flag:
(defthm rip-of-set-flag (equal (rip (set-flag flag val x86)) (rip x86)) :hints (("Goal" :in-theory (enable set-flag))))
(defthm rax-of-set-flag (equal (rax (set-flag flg val x86)) (rax x86)) :hints (("Goal" :in-theory (enable rax))))
(defthm rbx-of-set-flag (equal (rbx (set-flag flg val x86)) (rbx x86)) :hints (("Goal" :in-theory (enable rbx))))
(defthm rcx-of-set-flag (equal (rcx (set-flag flg val x86)) (rcx x86)) :hints (("Goal" :in-theory (enable rcx))))
(defthm rdx-of-set-flag (equal (rdx (set-flag flg val x86)) (rdx x86)) :hints (("Goal" :in-theory (enable rdx))))
(defthm rsi-of-set-flag (equal (rsi (set-flag flg val x86)) (rsi x86)) :hints (("Goal" :in-theory (enable rsi))))
(defthm rdi-of-set-flag (equal (rdi (set-flag flg val x86)) (rdi x86)) :hints (("Goal" :in-theory (enable rdi))))
(defthm r8-of-set-flag (equal (r8 (set-flag flg val x86)) (r8 x86)) :hints (("Goal" :in-theory (enable r8))))
(defthm r9-of-set-flag (equal (r9 (set-flag flg val x86)) (r9 x86)) :hints (("Goal" :in-theory (enable r9))))
(defthm r10-of-set-flag (equal (r10 (set-flag flg val x86)) (r10 x86)) :hints (("Goal" :in-theory (enable r10))))
(defthm r11-of-set-flag (equal (r11 (set-flag flg val x86)) (r11 x86)) :hints (("Goal" :in-theory (enable r11))))
(defthm r12-of-set-flag (equal (r12 (set-flag flg val x86)) (r12 x86)) :hints (("Goal" :in-theory (enable r12))))
(defthm r13-of-set-flag (equal (r13 (set-flag flg val x86)) (r13 x86)) :hints (("Goal" :in-theory (enable r13))))
(defthm r14-of-set-flag (equal (r14 (set-flag flg val x86)) (r14 x86)) :hints (("Goal" :in-theory (enable r14))))
(defthm r15-of-set-flag (equal (r15 (set-flag flg val x86)) (r15 x86)) :hints (("Goal" :in-theory (enable r15))))
(defthm rsp-of-set-flag (equal (rsp (set-flag flg val x86)) (rsp x86)) :hints (("Goal" :in-theory (enable rsp))))
(defthm rbp-of-set-flag (equal (rbp (set-flag flg val x86)) (rbp x86)) :hints (("Goal" :in-theory (enable rbp))))

;; Drop these?
;; (defthm rip-of-set-ms (equal (rip (set-ms val x86)) (rip x86)) :hints (("Goal" :in-theory (enable set-ms))))
;; (defthm rax-of-set-ms (equal (rax (set-ms val x86)) (rax x86)) :hints (("Goal" :in-theory (enable rax set-ms))))
;; (defthm rbx-of-set-ms (equal (rbx (set-ms val x86)) (rbx x86)) :hints (("Goal" :in-theory (enable rbx set-ms))))
;; (defthm rcx-of-set-ms (equal (rcx (set-ms val x86)) (rcx x86)) :hints (("Goal" :in-theory (enable rcx set-ms))))
;; (defthm rdx-of-set-ms (equal (rdx (set-ms val x86)) (rdx x86)) :hints (("Goal" :in-theory (enable rdx set-ms))))
;; (defthm rsi-of-set-ms (equal (rsi (set-ms val x86)) (rsi x86)) :hints (("Goal" :in-theory (enable rsi set-ms))))
;; (defthm rdi-of-set-ms (equal (rdi (set-ms val x86)) (rdi x86)) :hints (("Goal" :in-theory (enable rdi set-ms))))
;; (defthm r8-of-set-ms (equal (r8 (set-ms val x86)) (r8 x86)) :hints (("Goal" :in-theory (enable r8 set-ms))))
;; (defthm r9-of-set-ms (equal (r9 (set-ms val x86)) (r9 x86)) :hints (("Goal" :in-theory (enable r9 set-ms))))
;; (defthm r10-of-set-ms (equal (r10 (set-ms val x86)) (r10 x86)) :hints (("Goal" :in-theory (enable r10 set-ms))))
;; (defthm r11-of-set-ms (equal (r11 (set-ms val x86)) (r11 x86)) :hints (("Goal" :in-theory (enable r11 set-ms))))
;; (defthm r12-of-set-ms (equal (r12 (set-ms val x86)) (r12 x86)) :hints (("Goal" :in-theory (enable r12 set-ms))))
;; (defthm r13-of-set-ms (equal (r13 (set-ms val x86)) (r13 x86)) :hints (("Goal" :in-theory (enable r13 set-ms))))
;; (defthm r14-of-set-ms (equal (r14 (set-ms val x86)) (r14 x86)) :hints (("Goal" :in-theory (enable r14 set-ms))))
;; (defthm r15-of-set-ms (equal (r15 (set-ms val x86)) (r15 x86)) :hints (("Goal" :in-theory (enable r15 set-ms))))
;; (defthm rsp-of-set-ms (equal (rsp (set-ms val x86)) (rsp x86)) :hints (("Goal" :in-theory (enable rsp set-ms))))
;; (defthm rbp-of-set-ms (equal (rbp (set-ms val x86)) (rbp x86)) :hints (("Goal" :in-theory (enable rbp set-ms))))

(defthm rip-of-set-mxcsr (equal (rip (set-mxcsr val x86)) (rip x86)) :hints (("Goal" :in-theory (enable set-mxcsr))))
(defthm rax-of-set-mxcsr (equal (rax (set-mxcsr val x86)) (rax x86)) :hints (("Goal" :in-theory (enable rax set-mxcsr))))
(defthm rbx-of-set-mxcsr (equal (rbx (set-mxcsr val x86)) (rbx x86)) :hints (("Goal" :in-theory (enable rbx set-mxcsr))))
(defthm rcx-of-set-mxcsr (equal (rcx (set-mxcsr val x86)) (rcx x86)) :hints (("Goal" :in-theory (enable rcx set-mxcsr))))
(defthm rdx-of-set-mxcsr (equal (rdx (set-mxcsr val x86)) (rdx x86)) :hints (("Goal" :in-theory (enable rdx set-mxcsr))))
(defthm rsi-of-set-mxcsr (equal (rsi (set-mxcsr val x86)) (rsi x86)) :hints (("Goal" :in-theory (enable rsi set-mxcsr))))
(defthm rdi-of-set-mxcsr (equal (rdi (set-mxcsr val x86)) (rdi x86)) :hints (("Goal" :in-theory (enable rdi set-mxcsr))))
(defthm r8-of-set-mxcsr (equal (r8 (set-mxcsr val x86)) (r8 x86)) :hints (("Goal" :in-theory (enable r8 set-mxcsr))))
(defthm r9-of-set-mxcsr (equal (r9 (set-mxcsr val x86)) (r9 x86)) :hints (("Goal" :in-theory (enable r9 set-mxcsr))))
(defthm r10-of-set-mxcsr (equal (r10 (set-mxcsr val x86)) (r10 x86)) :hints (("Goal" :in-theory (enable r10 set-mxcsr))))
(defthm r11-of-set-mxcsr (equal (r11 (set-mxcsr val x86)) (r11 x86)) :hints (("Goal" :in-theory (enable r11 set-mxcsr))))
(defthm r12-of-set-mxcsr (equal (r12 (set-mxcsr val x86)) (r12 x86)) :hints (("Goal" :in-theory (enable r12 set-mxcsr))))
(defthm r13-of-set-mxcsr (equal (r13 (set-mxcsr val x86)) (r13 x86)) :hints (("Goal" :in-theory (enable r13 set-mxcsr))))
(defthm r14-of-set-mxcsr (equal (r14 (set-mxcsr val x86)) (r14 x86)) :hints (("Goal" :in-theory (enable r14 set-mxcsr))))
(defthm r15-of-set-mxcsr (equal (r15 (set-mxcsr val x86)) (r15 x86)) :hints (("Goal" :in-theory (enable r15 set-mxcsr))))
(defthm rsp-of-set-mxcsr (equal (rsp (set-mxcsr val x86)) (rsp x86)) :hints (("Goal" :in-theory (enable rsp set-mxcsr))))
(defthm rbp-of-set-mxcsr (equal (rbp (set-mxcsr val x86)) (rbp x86)) :hints (("Goal" :in-theory (enable rbp set-mxcsr))))

(defthm rip-of-set-undef (equal (rip (set-undef val x86)) (rip x86)) :hints (("Goal" :in-theory (enable set-undef))))
(defthm rax-of-set-undef (equal (rax (set-undef val x86)) (rax x86)) :hints (("Goal" :in-theory (enable rax set-undef))))
(defthm rbx-of-set-undef (equal (rbx (set-undef val x86)) (rbx x86)) :hints (("Goal" :in-theory (enable rbx set-undef))))
(defthm rcx-of-set-undef (equal (rcx (set-undef val x86)) (rcx x86)) :hints (("Goal" :in-theory (enable rcx set-undef))))
(defthm rdx-of-set-undef (equal (rdx (set-undef val x86)) (rdx x86)) :hints (("Goal" :in-theory (enable rdx set-undef))))
(defthm rsi-of-set-undef (equal (rsi (set-undef val x86)) (rsi x86)) :hints (("Goal" :in-theory (enable rsi set-undef))))
(defthm rdi-of-set-undef (equal (rdi (set-undef val x86)) (rdi x86)) :hints (("Goal" :in-theory (enable rdi set-undef))))
(defthm r8-of-set-undef (equal (r8 (set-undef val x86)) (r8 x86)) :hints (("Goal" :in-theory (enable r8 set-undef))))
(defthm r9-of-set-undef (equal (r9 (set-undef val x86)) (r9 x86)) :hints (("Goal" :in-theory (enable r9 set-undef))))
(defthm r10-of-set-undef (equal (r10 (set-undef val x86)) (r10 x86)) :hints (("Goal" :in-theory (enable r10 set-undef))))
(defthm r11-of-set-undef (equal (r11 (set-undef val x86)) (r11 x86)) :hints (("Goal" :in-theory (enable r11 set-undef))))
(defthm r12-of-set-undef (equal (r12 (set-undef val x86)) (r12 x86)) :hints (("Goal" :in-theory (enable r12 set-undef))))
(defthm r13-of-set-undef (equal (r13 (set-undef val x86)) (r13 x86)) :hints (("Goal" :in-theory (enable r13 set-undef))))
(defthm r14-of-set-undef (equal (r14 (set-undef val x86)) (r14 x86)) :hints (("Goal" :in-theory (enable r14 set-undef))))
(defthm r15-of-set-undef (equal (r15 (set-undef val x86)) (r15 x86)) :hints (("Goal" :in-theory (enable r15 set-undef))))
(defthm rsp-of-set-undef (equal (rsp (set-undef val x86)) (rsp x86)) :hints (("Goal" :in-theory (enable rsp set-undef))))
(defthm rbp-of-set-undef (equal (rbp (set-undef val x86)) (rbp x86)) :hints (("Goal" :in-theory (enable rbp set-undef))))

(defthm rip-of-write-byte (equal (rip (write-byte base-addr byte x86)) (rip x86)) :hints (("Goal" :in-theory (enable write-byte))))
(defthm rax-of-write-byte (equal (rax (write-byte base-addr byte x86)) (rax x86)) :hints (("Goal" :in-theory (enable write-byte))))
(defthm rbx-of-write-byte (equal (rbx (write-byte base-addr byte x86)) (rbx x86)) :hints (("Goal" :in-theory (enable write-byte))))
(defthm rcx-of-write-byte (equal (rcx (write-byte base-addr byte x86)) (rcx x86)) :hints (("Goal" :in-theory (enable write-byte))))
(defthm rdx-of-write-byte (equal (rdx (write-byte base-addr byte x86)) (rdx x86)) :hints (("Goal" :in-theory (enable write-byte))))
(defthm rsi-of-write-byte (equal (rsi (write-byte base-addr byte x86)) (rsi x86)) :hints (("Goal" :in-theory (enable write-byte))))
(defthm rdi-of-write-byte (equal (rdi (write-byte base-addr byte x86)) (rdi x86)) :hints (("Goal" :in-theory (enable write-byte))))
(defthm r8-of-write-byte (equal (r8 (write-byte base-addr byte x86)) (r8 x86)) :hints (("Goal" :in-theory (enable write-byte))))
(defthm r9-of-write-byte (equal (r9 (write-byte base-addr byte x86)) (r9 x86)) :hints (("Goal" :in-theory (enable write-byte))))
(defthm r10-of-write-byte (equal (r10 (write-byte base-addr byte x86)) (r10 x86)) :hints (("Goal" :in-theory (enable write-byte))))
(defthm r11-of-write-byte (equal (r11 (write-byte base-addr byte x86)) (r11 x86)) :hints (("Goal" :in-theory (enable write-byte))))
(defthm r12-of-write-byte (equal (r12 (write-byte base-addr byte x86)) (r12 x86)) :hints (("Goal" :in-theory (enable write-byte))))
(defthm r13-of-write-byte (equal (r13 (write-byte base-addr byte x86)) (r13 x86)) :hints (("Goal" :in-theory (enable write-byte))))
(defthm r14-of-write-byte (equal (r14 (write-byte base-addr byte x86)) (r14 x86)) :hints (("Goal" :in-theory (enable write-byte))))
(defthm r15-of-write-byte (equal (r15 (write-byte base-addr byte x86)) (r15 x86)) :hints (("Goal" :in-theory (enable write-byte))))
(defthm rsp-of-write-byte (equal (rsp (write-byte base-addr byte x86)) (rsp x86)) :hints (("Goal" :in-theory (enable write-byte))))
(defthm rbp-of-write-byte (equal (rbp (write-byte base-addr byte x86)) (rbp x86)) :hints (("Goal" :in-theory (enable write-byte))))

(defthm rip-of-write (equal (rip (write n base-addr val x86)) (rip x86)) :hints (("Goal" :in-theory (enable write))))
(defthm rax-of-write (equal (rax (write n base-addr val x86)) (rax x86)) :hints (("Goal" :in-theory (enable write))))
(defthm rbx-of-write (equal (rbx (write n base-addr val x86)) (rbx x86)) :hints (("Goal" :in-theory (enable write))))
(defthm rcx-of-write (equal (rcx (write n base-addr val x86)) (rcx x86)) :hints (("Goal" :in-theory (enable write))))
(defthm rdx-of-write (equal (rdx (write n base-addr val x86)) (rdx x86)) :hints (("Goal" :in-theory (enable write))))
(defthm rsi-of-write (equal (rsi (write n base-addr val x86)) (rsi x86)) :hints (("Goal" :in-theory (enable write))))
(defthm rdi-of-write (equal (rdi (write n base-addr val x86)) (rdi x86)) :hints (("Goal" :in-theory (enable write))))
(defthm r8-of-write (equal (r8 (write n base-addr val x86)) (r8 x86)) :hints (("Goal" :in-theory (enable write))))
(defthm r9-of-write (equal (r9 (write n base-addr val x86)) (r9 x86)) :hints (("Goal" :in-theory (enable write))))
(defthm r10-of-write (equal (r10 (write n base-addr val x86)) (r10 x86)) :hints (("Goal" :in-theory (enable write))))
(defthm r11-of-write (equal (r11 (write n base-addr val x86)) (r11 x86)) :hints (("Goal" :in-theory (enable write))))
(defthm r12-of-write (equal (r12 (write n base-addr val x86)) (r12 x86)) :hints (("Goal" :in-theory (enable write))))
(defthm r13-of-write (equal (r13 (write n base-addr val x86)) (r13 x86)) :hints (("Goal" :in-theory (enable write))))
(defthm r14-of-write (equal (r14 (write n base-addr val x86)) (r14 x86)) :hints (("Goal" :in-theory (enable write))))
(defthm r15-of-write (equal (r15 (write n base-addr val x86)) (r15 x86)) :hints (("Goal" :in-theory (enable write))))
(defthm rsp-of-write (equal (rsp (write n base-addr val x86)) (rsp x86)) :hints (("Goal" :in-theory (enable write))))
(defthm rbp-of-write (equal (rbp (write n base-addr val x86)) (rbp x86)) :hints (("Goal" :in-theory (enable write))))

(defthm rip-of-write-bytes (equal (rip (write-bytes base-addr vals x86)) (rip x86)) :hints (("Goal" :in-theory (enable write-bytes))))
(defthm rax-of-write-bytes (equal (rax (write-bytes base-addr vals x86)) (rax x86)) :hints (("Goal" :in-theory (enable write-bytes))))
(defthm rbx-of-write-bytes (equal (rbx (write-bytes base-addr vals x86)) (rbx x86)) :hints (("Goal" :in-theory (enable write-bytes))))
(defthm rcx-of-write-bytes (equal (rcx (write-bytes base-addr vals x86)) (rcx x86)) :hints (("Goal" :in-theory (enable write-bytes))))
(defthm rdx-of-write-bytes (equal (rdx (write-bytes base-addr vals x86)) (rdx x86)) :hints (("Goal" :in-theory (enable write-bytes))))
(defthm rsi-of-write-bytes (equal (rsi (write-bytes base-addr vals x86)) (rsi x86)) :hints (("Goal" :in-theory (enable write-bytes))))
(defthm rdi-of-write-bytes (equal (rdi (write-bytes base-addr vals x86)) (rdi x86)) :hints (("Goal" :in-theory (enable write-bytes))))
(defthm r8-of-write-bytes (equal (r8 (write-bytes base-addr vals x86)) (r8 x86)) :hints (("Goal" :in-theory (enable write-bytes))))
(defthm r9-of-write-bytes (equal (r9 (write-bytes base-addr vals x86)) (r9 x86)) :hints (("Goal" :in-theory (enable write-bytes))))
(defthm r10-of-write-bytes (equal (r10 (write-bytes base-addr vals x86)) (r10 x86)) :hints (("Goal" :in-theory (enable write-bytes))))
(defthm r11-of-write-bytes (equal (r11 (write-bytes base-addr vals x86)) (r11 x86)) :hints (("Goal" :in-theory (enable write-bytes))))
(defthm r12-of-write-bytes (equal (r12 (write-bytes base-addr vals x86)) (r12 x86)) :hints (("Goal" :in-theory (enable write-bytes))))
(defthm r13-of-write-bytes (equal (r13 (write-bytes base-addr vals x86)) (r13 x86)) :hints (("Goal" :in-theory (enable write-bytes))))
(defthm r14-of-write-bytes (equal (r14 (write-bytes base-addr vals x86)) (r14 x86)) :hints (("Goal" :in-theory (enable write-bytes))))
(defthm r15-of-write-bytes (equal (r15 (write-bytes base-addr vals x86)) (r15 x86)) :hints (("Goal" :in-theory (enable write-bytes))))
(defthm rsp-of-write-bytes (equal (rsp (write-bytes base-addr vals x86)) (rsp x86)) :hints (("Goal" :in-theory (enable write-bytes))))
(defthm rbp-of-write-bytes (equal (rbp (write-bytes base-addr vals x86)) (rbp x86)) :hints (("Goal" :in-theory (enable write-bytes))))

;;(defthm rip-of-!rflags (equal (rip (!rflags flags x86)) (rip x86)) :hints (("Goal" :in-theory (enable rip)))) ; not needed?
(defthm rax-of-!rflags (equal (rax (!rflags flags x86)) (rax x86)) :hints (("Goal" :in-theory (enable rax))))
(defthm rbx-of-!rflags (equal (rbx (!rflags flags x86)) (rbx x86)) :hints (("Goal" :in-theory (enable rbx))))
(defthm rcx-of-!rflags (equal (rcx (!rflags flags x86)) (rcx x86)) :hints (("Goal" :in-theory (enable rcx))))
(defthm rdx-of-!rflags (equal (rdx (!rflags flags x86)) (rdx x86)) :hints (("Goal" :in-theory (enable rdx))))
(defthm rsi-of-!rflags (equal (rsi (!rflags flags x86)) (rsi x86)) :hints (("Goal" :in-theory (enable rsi))))
(defthm rdi-of-!rflags (equal (rdi (!rflags flags x86)) (rdi x86)) :hints (("Goal" :in-theory (enable rdi))))
(defthm r8-of-!rflags (equal (r8 (!rflags flags x86)) (r8 x86)) :hints (("Goal" :in-theory (enable r8))))
(defthm r9-of-!rflags (equal (r9 (!rflags flags x86)) (r9 x86)) :hints (("Goal" :in-theory (enable r9))))
(defthm r10-of-!rflags (equal (r10 (!rflags flags x86)) (r10 x86)) :hints (("Goal" :in-theory (enable r10))))
(defthm r11-of-!rflags (equal (r11 (!rflags flags x86)) (r11 x86)) :hints (("Goal" :in-theory (enable r11))))
(defthm r12-of-!rflags (equal (r12 (!rflags flags x86)) (r12 x86)) :hints (("Goal" :in-theory (enable r12))))
(defthm r13-of-!rflags (equal (r13 (!rflags flags x86)) (r13 x86)) :hints (("Goal" :in-theory (enable r13))))
(defthm r14-of-!rflags (equal (r14 (!rflags flags x86)) (r14 x86)) :hints (("Goal" :in-theory (enable r14))))
(defthm r15-of-!rflags (equal (r15 (!rflags flags x86)) (r15 x86)) :hints (("Goal" :in-theory (enable r15))))
(defthm rsp-of-!rflags (equal (rsp (!rflags flags x86)) (rsp x86)) :hints (("Goal" :in-theory (enable rsp))))
(defthm rbp-of-!rflags (equal (rbp (!rflags flags x86)) (rbp x86)) :hints (("Goal" :in-theory (enable rbp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This section contains rules for various readers applied to the 17 register writers (including SET-RIP)

(defthm read-of-set-rip (equal (read n addr (set-rip rip x86)) (read n addr x86)) :hints (("Goal" :in-theory (enable set-rip))))
(defthm read-of-set-rax (equal (read n addr (set-rax val x86)) (read n addr x86)) :hints (("Goal" :in-theory (enable set-rax))))
(defthm read-of-set-rbx (equal (read n addr (set-rbx val x86)) (read n addr x86)) :hints (("Goal" :in-theory (enable set-rbx))))
(defthm read-of-set-rcx (equal (read n addr (set-rcx val x86)) (read n addr x86)) :hints (("Goal" :in-theory (enable set-rcx))))
(defthm read-of-set-rdx (equal (read n addr (set-rdx val x86)) (read n addr x86)) :hints (("Goal" :in-theory (enable set-rdx))))
(defthm read-of-set-rsi (equal (read n addr (set-rsi val x86)) (read n addr x86)) :hints (("Goal" :in-theory (enable set-rsi))))
(defthm read-of-set-rdi (equal (read n addr (set-rdi val x86)) (read n addr x86)) :hints (("Goal" :in-theory (enable set-rdi))))
(defthm read-of-set-r8 (equal (read n addr (set-r8 val x86)) (read n addr x86)) :hints (("Goal" :in-theory (enable set-r8))))
(defthm read-of-set-r9 (equal (read n addr (set-r9 val x86)) (read n addr x86)) :hints (("Goal" :in-theory (enable set-r9))))
(defthm read-of-set-r10 (equal (read n addr (set-r10 val x86)) (read n addr x86)) :hints (("Goal" :in-theory (enable set-r10))))
(defthm read-of-set-r11 (equal (read n addr (set-r11 val x86)) (read n addr x86)) :hints (("Goal" :in-theory (enable set-r11))))
(defthm read-of-set-r12 (equal (read n addr (set-r12 val x86)) (read n addr x86)) :hints (("Goal" :in-theory (enable set-r12))))
(defthm read-of-set-r13 (equal (read n addr (set-r13 val x86)) (read n addr x86)) :hints (("Goal" :in-theory (enable set-r13))))
(defthm read-of-set-r14 (equal (read n addr (set-r14 val x86)) (read n addr x86)) :hints (("Goal" :in-theory (enable set-r14))))
(defthm read-of-set-r15 (equal (read n addr (set-r15 val x86)) (read n addr x86)) :hints (("Goal" :in-theory (enable set-r15))))
(defthm read-of-set-rsp (equal (read n addr (set-rsp val x86)) (read n addr x86)) :hints (("Goal" :in-theory (enable set-rsp))))
(defthm read-of-set-rbp (equal (read n addr (set-rbp val x86)) (read n addr x86)) :hints (("Goal" :in-theory (enable set-rbp))))

;; todo: are we considering READ to be a 64-bit notion, or should this be moved?
(defthm read-of-set-undef (equal (read n addr (set-undef val x86)) (read n addr x86)) :hints (("Goal" :in-theory (enable set-undef))))
(defthm read-of-set-mxcsr (equal (read n addr (set-mxcsr val x86)) (read n addr x86)) :hints (("Goal" :in-theory (enable set-mxcsr))))
;(defthm read-of-set-ms (equal (read n addr (set-ms val x86)) (read n addr x86)) :hints (("Goal" :in-theory (enable set-ms))))
;(defthm read-of-set-fault (equal (read n addr (set-fault val x86)) (read n addr x86)) :hints (("Goal" :in-theory (enable set-fault))))
(defthm read-of-!rflags (equal (read n addr (!rflags v x86)) (read n addr x86)) :hints (("Goal" :in-theory (enable read))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm read-byte-of-set-rip (equal (read-byte addr (set-rip rip x86)) (read-byte addr x86)) :hints (("Goal" :in-theory (enable set-rip))))
(defthm read-byte-of-set-rax (equal (read-byte addr (set-rax val x86)) (read-byte addr x86)) :hints (("Goal" :in-theory (enable set-rax))))
(defthm read-byte-of-set-rbx (equal (read-byte addr (set-rbx val x86)) (read-byte addr x86)) :hints (("Goal" :in-theory (enable set-rbx))))
(defthm read-byte-of-set-rcx (equal (read-byte addr (set-rcx val x86)) (read-byte addr x86)) :hints (("Goal" :in-theory (enable set-rcx))))
(defthm read-byte-of-set-rdx (equal (read-byte addr (set-rdx val x86)) (read-byte addr x86)) :hints (("Goal" :in-theory (enable set-rdx))))
(defthm read-byte-of-set-rsi (equal (read-byte addr (set-rsi val x86)) (read-byte addr x86)) :hints (("Goal" :in-theory (enable set-rsi))))
(defthm read-byte-of-set-rdi (equal (read-byte addr (set-rdi val x86)) (read-byte addr x86)) :hints (("Goal" :in-theory (enable set-rdi))))
(defthm read-byte-of-set-r8 (equal (read-byte addr (set-r8 val x86)) (read-byte addr x86)) :hints (("Goal" :in-theory (enable set-r8))))
(defthm read-byte-of-set-r9 (equal (read-byte addr (set-r9 val x86)) (read-byte addr x86)) :hints (("Goal" :in-theory (enable set-r9))))
(defthm read-byte-of-set-r10 (equal (read-byte addr (set-r10 val x86)) (read-byte addr x86)) :hints (("Goal" :in-theory (enable set-r10))))
(defthm read-byte-of-set-r11 (equal (read-byte addr (set-r11 val x86)) (read-byte addr x86)) :hints (("Goal" :in-theory (enable set-r11))))
(defthm read-byte-of-set-r12 (equal (read-byte addr (set-r12 val x86)) (read-byte addr x86)) :hints (("Goal" :in-theory (enable set-r12))))
(defthm read-byte-of-set-r13 (equal (read-byte addr (set-r13 val x86)) (read-byte addr x86)) :hints (("Goal" :in-theory (enable set-r13))))
(defthm read-byte-of-set-r14 (equal (read-byte addr (set-r14 val x86)) (read-byte addr x86)) :hints (("Goal" :in-theory (enable set-r14))))
(defthm read-byte-of-set-r15 (equal (read-byte addr (set-r15 val x86)) (read-byte addr x86)) :hints (("Goal" :in-theory (enable set-r15))))
(defthm read-byte-of-set-rsp (equal (read-byte addr (set-rsp val x86)) (read-byte addr x86)) :hints (("Goal" :in-theory (enable set-rsp))))
(defthm read-byte-of-set-rbp (equal (read-byte addr (set-rbp val x86)) (read-byte addr x86)) :hints (("Goal" :in-theory (enable set-rbp))))
(defthm read-byte-of-set-undef (equal (read-byte addr (set-undef val x86)) (read-byte addr x86)) :hints (("Goal" :in-theory (enable set-undef))))
(defthm read-byte-of-set-mxcsr (equal (read-byte addr (set-mxcsr val x86)) (read-byte addr x86)) :hints (("Goal" :in-theory (enable set-mxcsr))))
;(defthm read-byte-of-set-ms (equal (read-byte addr (set-ms val x86)) (read-byte addr x86)) :hints (("Goal" :in-theory (enable set-ms))))
;(defthm read-byte-of-set-fault (equal (read-byte addr (set-fault val x86)) (read-byte addr x86)) :hints (("Goal" :in-theory (enable set-fault))))
(defthm read-byte-of-!rflags (equal (read-byte addr (!rflags v x86)) (read-byte addr x86)) :hints (("Goal" :in-theory (enable read))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm undef-of-set-rip (equal (undef (set-rip rip x86)) (undef x86)) :hints (("Goal" :in-theory (enable undef))))
(defthm undef-of-set-rax (equal (undef (set-rax val x86)) (undef x86)) :hints (("Goal" :in-theory (enable undef set-rax))))
(defthm undef-of-set-rbx (equal (undef (set-rbx val x86)) (undef x86)) :hints (("Goal" :in-theory (enable undef set-rbx))))
(defthm undef-of-set-rcx (equal (undef (set-rcx val x86)) (undef x86)) :hints (("Goal" :in-theory (enable undef set-rcx))))
(defthm undef-of-set-rdx (equal (undef (set-rdx val x86)) (undef x86)) :hints (("Goal" :in-theory (enable undef set-rdx))))
(defthm undef-of-set-rsi (equal (undef (set-rsi val x86)) (undef x86)) :hints (("Goal" :in-theory (enable undef set-rsi))))
(defthm undef-of-set-rdi (equal (undef (set-rdi val x86)) (undef x86)) :hints (("Goal" :in-theory (enable undef set-rdi))))
(defthm undef-of-set-r8 (equal (undef (set-r8 val x86)) (undef x86)) :hints (("Goal" :in-theory (enable undef set-r8))))
(defthm undef-of-set-r9 (equal (undef (set-r9 val x86)) (undef x86)) :hints (("Goal" :in-theory (enable undef set-r9))))
(defthm undef-of-set-r10 (equal (undef (set-r10 val x86)) (undef x86)) :hints (("Goal" :in-theory (enable undef set-r10))))
(defthm undef-of-set-r11 (equal (undef (set-r11 val x86)) (undef x86)) :hints (("Goal" :in-theory (enable undef set-r11))))
(defthm undef-of-set-r12 (equal (undef (set-r12 val x86)) (undef x86)) :hints (("Goal" :in-theory (enable undef set-r12))))
(defthm undef-of-set-r13 (equal (undef (set-r13 val x86)) (undef x86)) :hints (("Goal" :in-theory (enable undef set-r13))))
(defthm undef-of-set-r14 (equal (undef (set-r14 val x86)) (undef x86)) :hints (("Goal" :in-theory (enable undef set-r14))))
(defthm undef-of-set-r15 (equal (undef (set-r15 val x86)) (undef x86)) :hints (("Goal" :in-theory (enable undef set-r15))))
(defthm undef-of-set-rsp (equal (undef (set-rsp val x86)) (undef x86)) :hints (("Goal" :in-theory (enable undef set-rsp))))
(defthm undef-of-set-rbp (equal (undef (set-rbp val x86)) (undef x86)) :hints (("Goal" :in-theory (enable undef set-rbp))))

(defthm undef-of-write-byte (equal (undef (write-byte base-addr byte x86)) (undef x86)) :hints (("Goal" :in-theory (enable write-byte undef))))
(defthm undef-of-write (equal (undef (write n base-addr val x86)) (undef x86)) :hints (("Goal" :in-theory (enable write))))
(defthm undef-of-write-bytes (implies (undef x86) (undef (write-bytes base-addr vals x86))) :hints (("Goal" :in-theory (enable write-bytes))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm mxcsr-of-set-rip (equal (mxcsr (set-rip rip x86)) (mxcsr x86)) :hints (("Goal" :in-theory (enable mxcsr))))
(defthm mxcsr-of-set-rax (equal (mxcsr (set-rax val x86)) (mxcsr x86)) :hints (("Goal" :in-theory (enable mxcsr set-rax))))
(defthm mxcsr-of-set-rbx (equal (mxcsr (set-rbx val x86)) (mxcsr x86)) :hints (("Goal" :in-theory (enable mxcsr set-rbx))))
(defthm mxcsr-of-set-rcx (equal (mxcsr (set-rcx val x86)) (mxcsr x86)) :hints (("Goal" :in-theory (enable mxcsr set-rcx))))
(defthm mxcsr-of-set-rdx (equal (mxcsr (set-rdx val x86)) (mxcsr x86)) :hints (("Goal" :in-theory (enable mxcsr set-rdx))))
(defthm mxcsr-of-set-rsi (equal (mxcsr (set-rsi val x86)) (mxcsr x86)) :hints (("Goal" :in-theory (enable mxcsr set-rsi))))
(defthm mxcsr-of-set-rdi (equal (mxcsr (set-rdi val x86)) (mxcsr x86)) :hints (("Goal" :in-theory (enable mxcsr set-rdi))))
(defthm mxcsr-of-set-r8 (equal (mxcsr (set-r8 val x86)) (mxcsr x86)) :hints (("Goal" :in-theory (enable mxcsr set-r8))))
(defthm mxcsr-of-set-r9 (equal (mxcsr (set-r9 val x86)) (mxcsr x86)) :hints (("Goal" :in-theory (enable mxcsr set-r9))))
(defthm mxcsr-of-set-r10 (equal (mxcsr (set-r10 val x86)) (mxcsr x86)) :hints (("Goal" :in-theory (enable mxcsr set-r10))))
(defthm mxcsr-of-set-r11 (equal (mxcsr (set-r11 val x86)) (mxcsr x86)) :hints (("Goal" :in-theory (enable mxcsr set-r11))))
(defthm mxcsr-of-set-r12 (equal (mxcsr (set-r12 val x86)) (mxcsr x86)) :hints (("Goal" :in-theory (enable mxcsr set-r12))))
(defthm mxcsr-of-set-r13 (equal (mxcsr (set-r13 val x86)) (mxcsr x86)) :hints (("Goal" :in-theory (enable mxcsr set-r13))))
(defthm mxcsr-of-set-r14 (equal (mxcsr (set-r14 val x86)) (mxcsr x86)) :hints (("Goal" :in-theory (enable mxcsr set-r14))))
(defthm mxcsr-of-set-r15 (equal (mxcsr (set-r15 val x86)) (mxcsr x86)) :hints (("Goal" :in-theory (enable mxcsr set-r15))))
(defthm mxcsr-of-set-rsp (equal (mxcsr (set-rsp val x86)) (mxcsr x86)) :hints (("Goal" :in-theory (enable mxcsr set-rsp))))
(defthm mxcsr-of-set-rbp (equal (mxcsr (set-rbp val x86)) (mxcsr x86)) :hints (("Goal" :in-theory (enable mxcsr set-rbp))))

(defthm mxcsr-of-write-byte (equal (mxcsr (write-byte base-addr byte x86)) (mxcsr x86)) :hints (("Goal" :in-theory (enable write-byte))))
(defthm mxcsr-of-write (equal (mxcsr (write n base-addr val x86)) (mxcsr x86)) :hints (("Goal" :in-theory (enable write))))
(defthm mxcsr-of-write-bytes (implies (mxcsr x86) (mxcsr (write-bytes base-addr vals x86))) :hints (("Goal" :in-theory (enable write-bytes))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm ms-of-set-rip (equal (ms (set-rip rip x86)) (ms x86)) :hints (("Goal" :in-theory (enable ms))))
(defthm ms-of-set-rax (equal (ms (set-rax val x86)) (ms x86)) :hints (("Goal" :in-theory (enable ms set-rax))))
(defthm ms-of-set-rbx (equal (ms (set-rbx val x86)) (ms x86)) :hints (("Goal" :in-theory (enable ms set-rbx))))
(defthm ms-of-set-rcx (equal (ms (set-rcx val x86)) (ms x86)) :hints (("Goal" :in-theory (enable ms set-rcx))))
(defthm ms-of-set-rdx (equal (ms (set-rdx val x86)) (ms x86)) :hints (("Goal" :in-theory (enable ms set-rdx))))
(defthm ms-of-set-rsi (equal (ms (set-rsi val x86)) (ms x86)) :hints (("Goal" :in-theory (enable ms set-rsi))))
(defthm ms-of-set-rdi (equal (ms (set-rdi val x86)) (ms x86)) :hints (("Goal" :in-theory (enable ms set-rdi))))
(defthm ms-of-set-r8 (equal (ms (set-r8 val x86)) (ms x86)) :hints (("Goal" :in-theory (enable ms set-r8))))
(defthm ms-of-set-r9 (equal (ms (set-r9 val x86)) (ms x86)) :hints (("Goal" :in-theory (enable ms set-r9))))
(defthm ms-of-set-r10 (equal (ms (set-r10 val x86)) (ms x86)) :hints (("Goal" :in-theory (enable ms set-r10))))
(defthm ms-of-set-r11 (equal (ms (set-r11 val x86)) (ms x86)) :hints (("Goal" :in-theory (enable ms set-r11))))
(defthm ms-of-set-r12 (equal (ms (set-r12 val x86)) (ms x86)) :hints (("Goal" :in-theory (enable ms set-r12))))
(defthm ms-of-set-r13 (equal (ms (set-r13 val x86)) (ms x86)) :hints (("Goal" :in-theory (enable ms set-r13))))
(defthm ms-of-set-r14 (equal (ms (set-r14 val x86)) (ms x86)) :hints (("Goal" :in-theory (enable ms set-r14))))
(defthm ms-of-set-r15 (equal (ms (set-r15 val x86)) (ms x86)) :hints (("Goal" :in-theory (enable ms set-r15))))
(defthm ms-of-set-rsp (equal (ms (set-rsp val x86)) (ms x86)) :hints (("Goal" :in-theory (enable ms set-rsp))))
(defthm ms-of-set-rbp (equal (ms (set-rbp val x86)) (ms x86)) :hints (("Goal" :in-theory (enable ms set-rbp))))

(defthm ms-of-write-byte (equal (ms (write-byte base-addr byte x86)) (ms x86)) :hints (("Goal" :in-theory (enable write-byte ms))))
(defthm ms-of-write (equal (ms (write n base-addr val x86)) (ms x86)) :hints (("Goal" :in-theory (enable write))))
(defthm ms-of-write-bytes (implies (ms x86) (ms (write-bytes base-addr vals x86))) :hints (("Goal" :in-theory (enable write-bytes))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm fault-of-set-rip (equal (fault (set-rip rip x86)) (fault x86)) :hints (("Goal" :in-theory (enable fault))))
(defthm fault-of-set-rax (equal (fault (set-rax val x86)) (fault x86)) :hints (("Goal" :in-theory (enable fault set-rax))))
(defthm fault-of-set-rbx (equal (fault (set-rbx val x86)) (fault x86)) :hints (("Goal" :in-theory (enable fault set-rbx))))
(defthm fault-of-set-rcx (equal (fault (set-rcx val x86)) (fault x86)) :hints (("Goal" :in-theory (enable fault set-rcx))))
(defthm fault-of-set-rdx (equal (fault (set-rdx val x86)) (fault x86)) :hints (("Goal" :in-theory (enable fault set-rdx))))
(defthm fault-of-set-rsi (equal (fault (set-rsi val x86)) (fault x86)) :hints (("Goal" :in-theory (enable fault set-rsi))))
(defthm fault-of-set-rdi (equal (fault (set-rdi val x86)) (fault x86)) :hints (("Goal" :in-theory (enable fault set-rdi))))
(defthm fault-of-set-r8 (equal (fault (set-r8 val x86)) (fault x86)) :hints (("Goal" :in-theory (enable fault set-r8))))
(defthm fault-of-set-r9 (equal (fault (set-r9 val x86)) (fault x86)) :hints (("Goal" :in-theory (enable fault set-r9))))
(defthm fault-of-set-r10 (equal (fault (set-r10 val x86)) (fault x86)) :hints (("Goal" :in-theory (enable fault set-r10))))
(defthm fault-of-set-r11 (equal (fault (set-r11 val x86)) (fault x86)) :hints (("Goal" :in-theory (enable fault set-r11))))
(defthm fault-of-set-r12 (equal (fault (set-r12 val x86)) (fault x86)) :hints (("Goal" :in-theory (enable fault set-r12))))
(defthm fault-of-set-r13 (equal (fault (set-r13 val x86)) (fault x86)) :hints (("Goal" :in-theory (enable fault set-r13))))
(defthm fault-of-set-r14 (equal (fault (set-r14 val x86)) (fault x86)) :hints (("Goal" :in-theory (enable fault set-r14))))
(defthm fault-of-set-r15 (equal (fault (set-r15 val x86)) (fault x86)) :hints (("Goal" :in-theory (enable fault set-r15))))
(defthm fault-of-set-rsp (equal (fault (set-rsp val x86)) (fault x86)) :hints (("Goal" :in-theory (enable fault set-rsp))))
(defthm fault-of-set-rbp (equal (fault (set-rbp val x86)) (fault x86)) :hints (("Goal" :in-theory (enable fault set-rbp))))

(defthm fault-of-write-byte (equal (fault (write-byte base-addr byte x86)) (fault x86)) :hints (("Goal" :in-theory (enable write-byte fault))))
(defthm fault-of-write (equal (fault (write n base-addr val x86)) (fault x86)) :hints (("Goal" :in-theory (enable write))))
(defthm fault-of-write-bytes (implies (fault x86) (fault (write-bytes base-addr vals x86))) :hints (("Goal" :in-theory (enable write-bytes))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm x86p-of-set-rip (implies (x86p x86) (x86p (set-rip rip x86))) :hints (("Goal" :in-theory (enable set-rip))))
(defthm x86p-of-set-rax (implies (x86p x86) (x86p (set-rax rax x86))) :hints (("Goal" :in-theory (enable set-rax))))
(defthm x86p-of-set-rbx (implies (x86p x86) (x86p (set-rbx rbx x86))) :hints (("Goal" :in-theory (enable set-rbx))))
(defthm x86p-of-set-rcx (implies (x86p x86) (x86p (set-rcx rcx x86))) :hints (("Goal" :in-theory (enable set-rcx))))
(defthm x86p-of-set-rdx (implies (x86p x86) (x86p (set-rdx rdx x86))) :hints (("Goal" :in-theory (enable set-rdx))))
(defthm x86p-of-set-rsi (implies (x86p x86) (x86p (set-rsi rsi x86))) :hints (("Goal" :in-theory (enable set-rsi))))
(defthm x86p-of-set-rdi (implies (x86p x86) (x86p (set-rdi rdi x86))) :hints (("Goal" :in-theory (enable set-rdi))))
(defthm x86p-of-set-r8 (implies (x86p x86) (x86p (set-r8 r8 x86))) :hints (("Goal" :in-theory (enable set-r8))))
(defthm x86p-of-set-r9 (implies (x86p x86) (x86p (set-r9 r9 x86))) :hints (("Goal" :in-theory (enable set-r9))))
(defthm x86p-of-set-r10 (implies (x86p x86) (x86p (set-r10 r10 x86))) :hints (("Goal" :in-theory (enable set-r10))))
(defthm x86p-of-set-r11 (implies (x86p x86) (x86p (set-r11 r11 x86))) :hints (("Goal" :in-theory (enable set-r11))))
(defthm x86p-of-set-r12 (implies (x86p x86) (x86p (set-r12 r12 x86))) :hints (("Goal" :in-theory (enable set-r12))))
(defthm x86p-of-set-r13 (implies (x86p x86) (x86p (set-r13 r13 x86))) :hints (("Goal" :in-theory (enable set-r13))))
(defthm x86p-of-set-r14 (implies (x86p x86) (x86p (set-r14 r14 x86))) :hints (("Goal" :in-theory (enable set-r14))))
(defthm x86p-of-set-r15 (implies (x86p x86) (x86p (set-r15 r15 x86))) :hints (("Goal" :in-theory (enable set-r15))))
(defthm x86p-of-set-rsp (implies (x86p x86) (x86p (set-rsp rsp x86))) :hints (("Goal" :in-theory (enable set-rsp))))
(defthm x86p-of-set-rbp (implies (x86p x86) (x86p (set-rbp rbp x86))) :hints (("Goal" :in-theory (enable set-rbp))))

(defthm x86p-of-write-byte (implies (x86p x86) (x86p (write-byte base-addr byte x86))) :hints (("Goal" :in-theory (enable write-byte))))
(defthm x86p-of-write (implies (x86p x86) (x86p (write n base-addr val x86))) :hints (("Goal" :in-theory (enable write))))
(defthm x86p-of-write-bytes (implies (x86p x86) (x86p (write-bytes base-addr vals x86))) :hints (("Goal" :in-theory (enable write-bytes))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm alignment-checking-enabled-p-of-set-rip (equal (alignment-checking-enabled-p (set-rip rip x86)) (alignment-checking-enabled-p x86)) :hints (("Goal" :in-theory (enable set-rip))))
(defthm alignment-checking-enabled-p-of-set-rax (equal (alignment-checking-enabled-p (set-rax rax x86)) (alignment-checking-enabled-p x86)) :hints (("Goal" :in-theory (enable set-rax))))
(defthm alignment-checking-enabled-p-of-set-rbx (equal (alignment-checking-enabled-p (set-rbx rbx x86)) (alignment-checking-enabled-p x86)) :hints (("Goal" :in-theory (enable set-rbx))))
(defthm alignment-checking-enabled-p-of-set-rcx (equal (alignment-checking-enabled-p (set-rcx rcx x86)) (alignment-checking-enabled-p x86)) :hints (("Goal" :in-theory (enable set-rcx))))
(defthm alignment-checking-enabled-p-of-set-rdx (equal (alignment-checking-enabled-p (set-rdx rdx x86)) (alignment-checking-enabled-p x86)) :hints (("Goal" :in-theory (enable set-rdx))))
(defthm alignment-checking-enabled-p-of-set-rsi (equal (alignment-checking-enabled-p (set-rsi rsi x86)) (alignment-checking-enabled-p x86)) :hints (("Goal" :in-theory (enable set-rsi))))
(defthm alignment-checking-enabled-p-of-set-rdi (equal (alignment-checking-enabled-p (set-rdi rdi x86)) (alignment-checking-enabled-p x86)) :hints (("Goal" :in-theory (enable set-rdi))))
(defthm alignment-checking-enabled-p-of-set-r8 (equal (alignment-checking-enabled-p (set-r8 r8 x86)) (alignment-checking-enabled-p x86)) :hints (("Goal" :in-theory (enable set-r8))))
(defthm alignment-checking-enabled-p-of-set-r9 (equal (alignment-checking-enabled-p (set-r9 r9 x86)) (alignment-checking-enabled-p x86)) :hints (("Goal" :in-theory (enable set-r9))))
(defthm alignment-checking-enabled-p-of-set-r10 (equal (alignment-checking-enabled-p (set-r10 r10 x86)) (alignment-checking-enabled-p x86)) :hints (("Goal" :in-theory (enable set-r10))))
(defthm alignment-checking-enabled-p-of-set-r11 (equal (alignment-checking-enabled-p (set-r11 r11 x86)) (alignment-checking-enabled-p x86)) :hints (("Goal" :in-theory (enable set-r11))))
(defthm alignment-checking-enabled-p-of-set-r12 (equal (alignment-checking-enabled-p (set-r12 r12 x86)) (alignment-checking-enabled-p x86)) :hints (("Goal" :in-theory (enable set-r12))))
(defthm alignment-checking-enabled-p-of-set-r13 (equal (alignment-checking-enabled-p (set-r13 r13 x86)) (alignment-checking-enabled-p x86)) :hints (("Goal" :in-theory (enable set-r13))))
(defthm alignment-checking-enabled-p-of-set-r14 (equal (alignment-checking-enabled-p (set-r14 r14 x86)) (alignment-checking-enabled-p x86)) :hints (("Goal" :in-theory (enable set-r14))))
(defthm alignment-checking-enabled-p-of-set-r15 (equal (alignment-checking-enabled-p (set-r15 r15 x86)) (alignment-checking-enabled-p x86)) :hints (("Goal" :in-theory (enable set-r15))))
(defthm alignment-checking-enabled-p-of-set-rsp (equal (alignment-checking-enabled-p (set-rsp rsp x86)) (alignment-checking-enabled-p x86)) :hints (("Goal" :in-theory (enable set-rsp))))
(defthm alignment-checking-enabled-p-of-set-rbp (equal (alignment-checking-enabled-p (set-rbp rbp x86)) (alignment-checking-enabled-p x86)) :hints (("Goal" :in-theory (enable set-rbp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm get-flag-of-set-rip (equal (get-flag flag (set-rip rip x86)) (get-flag flag x86)) :hints (("Goal" :in-theory (enable set-rip))))
(defthm get-flag-of-set-rax (equal (get-flag flag (set-rax rax x86)) (get-flag flag x86)) :hints (("Goal" :in-theory (enable set-rax))))
(defthm get-flag-of-set-rbx (equal (get-flag flag (set-rbx rbx x86)) (get-flag flag x86)) :hints (("Goal" :in-theory (enable set-rbx))))
(defthm get-flag-of-set-rcx (equal (get-flag flag (set-rcx rcx x86)) (get-flag flag x86)) :hints (("Goal" :in-theory (enable set-rcx))))
(defthm get-flag-of-set-rdx (equal (get-flag flag (set-rdx rdx x86)) (get-flag flag x86)) :hints (("Goal" :in-theory (enable set-rdx))))
(defthm get-flag-of-set-rsi (equal (get-flag flag (set-rsi rsi x86)) (get-flag flag x86)) :hints (("Goal" :in-theory (enable set-rsi))))
(defthm get-flag-of-set-rdi (equal (get-flag flag (set-rdi rdi x86)) (get-flag flag x86)) :hints (("Goal" :in-theory (enable set-rdi))))
(defthm get-flag-of-set-r8 (equal (get-flag flag (set-r8 r8 x86)) (get-flag flag x86)) :hints (("Goal" :in-theory (enable set-r8))))
(defthm get-flag-of-set-r9 (equal (get-flag flag (set-r9 r9 x86)) (get-flag flag x86)) :hints (("Goal" :in-theory (enable set-r9))))
(defthm get-flag-of-set-r10 (equal (get-flag flag (set-r10 r10 x86)) (get-flag flag x86)) :hints (("Goal" :in-theory (enable set-r10))))
(defthm get-flag-of-set-r11 (equal (get-flag flag (set-r11 r11 x86)) (get-flag flag x86)) :hints (("Goal" :in-theory (enable set-r11))))
(defthm get-flag-of-set-r12 (equal (get-flag flag (set-r12 r12 x86)) (get-flag flag x86)) :hints (("Goal" :in-theory (enable set-r12))))
(defthm get-flag-of-set-r13 (equal (get-flag flag (set-r13 r13 x86)) (get-flag flag x86)) :hints (("Goal" :in-theory (enable set-r13))))
(defthm get-flag-of-set-r14 (equal (get-flag flag (set-r14 r14 x86)) (get-flag flag x86)) :hints (("Goal" :in-theory (enable set-r14))))
(defthm get-flag-of-set-r15 (equal (get-flag flag (set-r15 r15 x86)) (get-flag flag x86)) :hints (("Goal" :in-theory (enable set-r15))))
(defthm get-flag-of-set-rsp (equal (get-flag flag (set-rsp rsp x86)) (get-flag flag x86)) :hints (("Goal" :in-theory (enable set-rsp))))
(defthm get-flag-of-set-rbp (equal (get-flag flag (set-rbp rbp x86)) (get-flag flag x86)) :hints (("Goal" :in-theory (enable set-rbp))))

;; (defthm eff-addr-okp-of-set-rax
;;   (equal (eff-addr-okp eff-addr seg-reg (set-rax rax x86))
;;          (eff-addr-okp eff-addr seg-reg x86))
;;   :hints (("Goal" :in-theory (enable set-rax))))

;; (defthm eff-addr-okp-of-set-rbx
;;   (equal (eff-addr-okp eff-addr seg-reg (set-rbx rbx x86))
;;          (eff-addr-okp eff-addr seg-reg x86))
;;   :hints (("Goal" :in-theory (enable set-rbx))))

;; (defthm eff-addr-okp-of-set-rcx
;;   (equal (eff-addr-okp eff-addr seg-reg (set-rcx rcx x86))
;;          (eff-addr-okp eff-addr seg-reg x86))
;;   :hints (("Goal" :in-theory (enable set-rcx))))

;; (defthm eff-addr-okp-of-set-rdx
;;   (equal (eff-addr-okp eff-addr seg-reg (set-rdx rdx x86))
;;          (eff-addr-okp eff-addr seg-reg x86))
;;   :hints (("Goal" :in-theory (enable set-rdx))))

;; (defthm eff-addr-okp-of-set-rsp
;;   (equal (eff-addr-okp eff-addr seg-reg (set-rsp rsp x86))
;;          (eff-addr-okp eff-addr seg-reg x86))
;;   :hints (("Goal" :in-theory (enable set-rsp))))

;; (defthm eff-addr-okp-of-set-rbp
;;   (equal (eff-addr-okp eff-addr seg-reg (set-rbp rbp x86))
;;          (eff-addr-okp eff-addr seg-reg x86))
;;   :hints (("Goal" :in-theory (enable set-rbp))))

;; ;;;

;; (defthm eff-addrs-okp-of-set-rax
;;   (equal (eff-addrs-okp n eff-addr seg-reg (set-rax rax x86))
;;          (eff-addrs-okp n eff-addr seg-reg x86))
;;   :hints (("Goal" :in-theory (enable set-rax))))

;; (defthm eff-addrs-okp-of-set-rbx
;;   (equal (eff-addrs-okp n eff-addr seg-reg (set-rbx rbx x86))
;;          (eff-addrs-okp n eff-addr seg-reg x86))
;;   :hints (("Goal" :in-theory (enable set-rbx))))

;; (defthm eff-addrs-okp-of-set-rcx
;;   (equal (eff-addrs-okp n eff-addr seg-reg (set-rcx rcx x86))
;;          (eff-addrs-okp n eff-addr seg-reg x86))
;;   :hints (("Goal" :in-theory (enable set-rcx))))

;; (defthm eff-addrs-okp-of-set-rdx
;;   (equal (eff-addrs-okp n eff-addr seg-reg (set-rdx rdx x86))
;;          (eff-addrs-okp n eff-addr seg-reg x86))
;;   :hints (("Goal" :in-theory (enable set-rdx))))

;; (defthm eff-addrs-okp-of-set-rsp
;;   (equal (eff-addrs-okp n eff-addr seg-reg (set-rsp rsp x86))
;;          (eff-addrs-okp n eff-addr seg-reg x86))
;;   :hints (("Goal" :in-theory (enable set-rsp))))

;; (defthm eff-addrs-okp-of-set-rbp
;;   (equal (eff-addrs-okp n eff-addr seg-reg (set-rbp rbp x86))
;;          (eff-addrs-okp n eff-addr seg-reg x86))
;;   :hints (("Goal" :in-theory (enable set-rbp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm 64-bit-modep-of-set-rip (equal (64-bit-modep (set-rip rip x86)) (64-bit-modep x86)) :hints (("Goal" :in-theory (enable set-rip))))
(defthm 64-bit-modep-of-set-rax (equal (64-bit-modep (set-rax rax x86)) (64-bit-modep x86)) :hints (("Goal" :in-theory (enable set-rax))))
(defthm 64-bit-modep-of-set-rbx (equal (64-bit-modep (set-rbx rbx x86)) (64-bit-modep x86)) :hints (("Goal" :in-theory (enable set-rbx))))
(defthm 64-bit-modep-of-set-rcx (equal (64-bit-modep (set-rcx rcx x86)) (64-bit-modep x86)) :hints (("Goal" :in-theory (enable set-rcx))))
(defthm 64-bit-modep-of-set-rdx (equal (64-bit-modep (set-rdx rdx x86)) (64-bit-modep x86)) :hints (("Goal" :in-theory (enable set-rdx))))
(defthm 64-bit-modep-of-set-rsi (equal (64-bit-modep (set-rsi rsi x86)) (64-bit-modep x86)) :hints (("Goal" :in-theory (enable set-rsi))))
(defthm 64-bit-modep-of-set-rdi (equal (64-bit-modep (set-rdi rdi x86)) (64-bit-modep x86)) :hints (("Goal" :in-theory (enable set-rdi))))
(defthm 64-bit-modep-of-set-r8 (equal (64-bit-modep (set-r8 r8 x86)) (64-bit-modep x86)) :hints (("Goal" :in-theory (enable set-r8))))
(defthm 64-bit-modep-of-set-r9 (equal (64-bit-modep (set-r9 r9 x86)) (64-bit-modep x86)) :hints (("Goal" :in-theory (enable set-r9))))
(defthm 64-bit-modep-of-set-r10 (equal (64-bit-modep (set-r10 r10 x86)) (64-bit-modep x86)) :hints (("Goal" :in-theory (enable set-r10))))
(defthm 64-bit-modep-of-set-r11 (equal (64-bit-modep (set-r11 r11 x86)) (64-bit-modep x86)) :hints (("Goal" :in-theory (enable set-r11))))
(defthm 64-bit-modep-of-set-r12 (equal (64-bit-modep (set-r12 r12 x86)) (64-bit-modep x86)) :hints (("Goal" :in-theory (enable set-r12))))
(defthm 64-bit-modep-of-set-r13 (equal (64-bit-modep (set-r13 r13 x86)) (64-bit-modep x86)) :hints (("Goal" :in-theory (enable set-r13))))
(defthm 64-bit-modep-of-set-r14 (equal (64-bit-modep (set-r14 r14 x86)) (64-bit-modep x86)) :hints (("Goal" :in-theory (enable set-r14))))
(defthm 64-bit-modep-of-set-r15 (equal (64-bit-modep (set-r15 r15 x86)) (64-bit-modep x86)) :hints (("Goal" :in-theory (enable set-r15))))
(defthm 64-bit-modep-of-set-rsp (equal (64-bit-modep (set-rsp rsp x86)) (64-bit-modep x86)) :hints (("Goal" :in-theory (enable set-rsp))))
(defthm 64-bit-modep-of-set-rbp (equal (64-bit-modep (set-rbp rbp x86)) (64-bit-modep x86)) :hints (("Goal" :in-theory (enable set-rbp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm app-view-of-set-rip (equal (app-view (set-rip rip x86)) (app-view x86)) :hints (("Goal" :in-theory (enable set-rip))))
(defthm app-view-of-set-rax (equal (app-view (set-rax rax x86)) (app-view x86)) :hints (("Goal" :in-theory (enable set-rax))))
(defthm app-view-of-set-rbx (equal (app-view (set-rbx rbx x86)) (app-view x86)) :hints (("Goal" :in-theory (enable set-rbx))))
(defthm app-view-of-set-rcx (equal (app-view (set-rcx rcx x86)) (app-view x86)) :hints (("Goal" :in-theory (enable set-rcx))))
(defthm app-view-of-set-rdx (equal (app-view (set-rdx rdx x86)) (app-view x86)) :hints (("Goal" :in-theory (enable set-rdx))))
(defthm app-view-of-set-rsi (equal (app-view (set-rsi rsi x86)) (app-view x86)) :hints (("Goal" :in-theory (enable set-rsi))))
(defthm app-view-of-set-rdi (equal (app-view (set-rdi rdi x86)) (app-view x86)) :hints (("Goal" :in-theory (enable set-rdi))))
(defthm app-view-of-set-r8 (equal (app-view (set-r8 r8 x86)) (app-view x86)) :hints (("Goal" :in-theory (enable set-r8))))
(defthm app-view-of-set-r9 (equal (app-view (set-r9 r9 x86)) (app-view x86)) :hints (("Goal" :in-theory (enable set-r9))))
(defthm app-view-of-set-r10 (equal (app-view (set-r10 r10 x86)) (app-view x86)) :hints (("Goal" :in-theory (enable set-r10))))
(defthm app-view-of-set-r11 (equal (app-view (set-r11 r11 x86)) (app-view x86)) :hints (("Goal" :in-theory (enable set-r11))))
(defthm app-view-of-set-r12 (equal (app-view (set-r12 r12 x86)) (app-view x86)) :hints (("Goal" :in-theory (enable set-r12))))
(defthm app-view-of-set-r13 (equal (app-view (set-r13 r13 x86)) (app-view x86)) :hints (("Goal" :in-theory (enable set-r13))))
(defthm app-view-of-set-r14 (equal (app-view (set-r14 r14 x86)) (app-view x86)) :hints (("Goal" :in-theory (enable set-r14))))
(defthm app-view-of-set-r15 (equal (app-view (set-r15 r15 x86)) (app-view x86)) :hints (("Goal" :in-theory (enable set-r15))))
(defthm app-view-of-set-rsp (equal (app-view (set-rsp rsp x86)) (app-view x86)) :hints (("Goal" :in-theory (enable set-rsp))))
(defthm app-view-of-set-rbp (equal (app-view (set-rbp rbp x86)) (app-view x86)) :hints (("Goal" :in-theory (enable set-rbp))))

;; (defthm app-view-of-write-to-segment
;;   (equal (app-view (write-to-segment n eff-addr seg-reg val x86))
;;          (app-view x86)))

;; ;;;

;; (defthm code-segment-assumptions32-for-code-of-set-rax
;;   (equal (code-segment-assumptions32-for-code code offset (set-rax rax x86))
;;          (code-segment-assumptions32-for-code code offset x86))
;;   :hints (("Goal" :in-theory (enable set-rax))))

;; (defthm code-segment-assumptions32-for-code-of-set-rbx
;;   (equal (code-segment-assumptions32-for-code code offset (set-rbx rbx x86))
;;          (code-segment-assumptions32-for-code code offset x86))
;;   :hints (("Goal" :in-theory (enable set-rbx))))

;; (defthm code-segment-assumptions32-for-code-of-set-rcx
;;   (equal (code-segment-assumptions32-for-code code offset (set-rcx rcx x86))
;;          (code-segment-assumptions32-for-code code offset x86))
;;   :hints (("Goal" :in-theory (enable set-rcx))))

;; (defthm code-segment-assumptions32-for-code-of-set-rdx
;;   (equal (code-segment-assumptions32-for-code code offset (set-rdx rdx x86))
;;          (code-segment-assumptions32-for-code code offset x86))
;;   :hints (("Goal" :in-theory (enable set-rdx))))

;; (defthm code-segment-assumptions32-for-code-of-set-rsp
;;   (equal (code-segment-assumptions32-for-code code offset (set-rsp rsp x86))
;;          (code-segment-assumptions32-for-code code offset x86))
;;   :hints (("Goal" :in-theory (enable set-rsp))))

;; (defthm code-segment-assumptions32-for-code-of-set-rbp
;;   (equal (code-segment-assumptions32-for-code code offset (set-rbp rbp x86))
;;          (code-segment-assumptions32-for-code code offset x86))
;;   :hints (("Goal" :in-theory (enable set-rbp))))

;; ;;;

;; (defthm segment-base-and-bounds-of-set-rax
;;   (equal (segment-base-and-bounds proc-mode seg-reg (set-rax rax x86))
;;          (segment-base-and-bounds proc-mode seg-reg x86))
;;   :hints (("Goal" :in-theory (enable set-rax))))

;; (defthm segment-base-and-bounds-of-set-rbx
;;   (equal (segment-base-and-bounds proc-mode seg-reg (set-rbx rbx x86))
;;          (segment-base-and-bounds proc-mode seg-reg x86))
;;   :hints (("Goal" :in-theory (enable set-rbx))))

;; (defthm segment-base-and-bounds-of-set-rcx
;;   (equal (segment-base-and-bounds proc-mode seg-reg (set-rcx rcx x86))
;;          (segment-base-and-bounds proc-mode seg-reg x86))
;;   :hints (("Goal" :in-theory (enable set-rcx))))

;; (defthm segment-base-and-bounds-of-set-rdx
;;   (equal (segment-base-and-bounds proc-mode seg-reg (set-rdx rdx x86))
;;          (segment-base-and-bounds proc-mode seg-reg x86))
;;   :hints (("Goal" :in-theory (enable set-rdx))))

;; (defthm segment-base-and-bounds-of-set-rsp
;;   (equal (segment-base-and-bounds proc-mode seg-reg (set-rsp rsp x86))
;;          (segment-base-and-bounds proc-mode seg-reg x86))
;;   :hints (("Goal" :in-theory (enable set-rsp))))

;; (defthm segment-base-and-bounds-of-set-rbp
;;   (equal (segment-base-and-bounds proc-mode seg-reg (set-rbp rbp x86))
;;          (segment-base-and-bounds proc-mode seg-reg x86))
;;   :hints (("Goal" :in-theory (enable set-rbp))))

;; ;;;

;; (defthm data-segment-writeable-bit-of-set-rip
;;   (equal (data-segment-writeable-bit seg-reg (set-rip rip x86))
;;          (data-segment-writeable-bit seg-reg x86))
;;   :hints (("Goal" :in-theory (enable set-rip))))

;; (defthm data-segment-writeable-bit-of-set-rax
;;   (equal (data-segment-writeable-bit seg-reg (set-rax rax x86))
;;          (data-segment-writeable-bit seg-reg x86))
;;   :hints (("Goal" :in-theory (enable set-rax))))

;; (defthm data-segment-writeable-bit-of-set-rbx
;;   (equal (data-segment-writeable-bit seg-reg (set-rbx rbx x86))
;;          (data-segment-writeable-bit seg-reg x86))
;;   :hints (("Goal" :in-theory (enable set-rbx))))

;; (defthm data-segment-writeable-bit-of-set-rcx
;;   (equal (data-segment-writeable-bit seg-reg (set-rcx rcx x86))
;;          (data-segment-writeable-bit seg-reg x86))
;;   :hints (("Goal" :in-theory (enable set-rcx))))

;; (defthm data-segment-writeable-bit-of-set-rdx
;;   (equal (data-segment-writeable-bit seg-reg (set-rdx rdx x86))
;;          (data-segment-writeable-bit seg-reg x86))
;;   :hints (("Goal" :in-theory (enable set-rdx))))

;; (defthm data-segment-writeable-bit-of-set-rsp
;;   (equal (data-segment-writeable-bit seg-reg (set-rsp rsp x86))
;;          (data-segment-writeable-bit seg-reg x86))
;;   :hints (("Goal" :in-theory (enable set-rsp))))

;; (defthm data-segment-writeable-bit-of-set-rbp
;;   (equal (data-segment-writeable-bit seg-reg (set-rbp rbp x86))
;;          (data-segment-writeable-bit seg-reg x86))
;;   :hints (("Goal" :in-theory (enable set-rbp))))

;; (defthm data-segment-writeable-bit-of-write-byte-to-segment
;;   (equal (data-segment-writeable-bit seg-reg1 (write-byte-to-segment eff-addr seg-reg2 val x86))
;;          (data-segment-writeable-bit seg-reg1 x86))
;;   :hints (("Goal" :in-theory (enable write-byte-to-segment))))

;; (defthm data-segment-writeable-bit-of-write-to-segment
;;   (equal (data-segment-writeable-bit seg-reg1 (write-to-segment n eff-addr seg-reg2 val x86))
;;          (data-segment-writeable-bit seg-reg1 x86))
;;   :hints (("Goal" :in-theory (enable write-to-segment))))

;; ;;;

;; (defthm code-segment-readable-bit-of-set-rip
;;   (equal (code-segment-readable-bit (set-rip rip x86))
;;          (code-segment-readable-bit x86))
;;   :hints (("Goal" :in-theory (enable set-rip))))

;; (defthm code-segment-readable-bit-of-set-rax
;;   (equal (code-segment-readable-bit (set-rax rax x86))
;;          (code-segment-readable-bit x86))
;;   :hints (("Goal" :in-theory (enable set-rax))))

;; (defthm code-segment-readable-bit-of-set-rbx
;;   (equal (code-segment-readable-bit (set-rbx rbx x86))
;;          (code-segment-readable-bit x86))
;;   :hints (("Goal" :in-theory (enable set-rbx))))

;; (defthm code-segment-readable-bit-of-set-rcx
;;   (equal (code-segment-readable-bit (set-rcx rcx x86))
;;          (code-segment-readable-bit x86))
;;   :hints (("Goal" :in-theory (enable set-rcx))))

;; (defthm code-segment-readable-bit-of-set-rdx
;;   (equal (code-segment-readable-bit (set-rdx rdx x86))
;;          (code-segment-readable-bit x86))
;;   :hints (("Goal" :in-theory (enable set-rdx))))

;; (defthm code-segment-readable-bit-of-set-rsp
;;   (equal (code-segment-readable-bit (set-rsp rsp x86))
;;          (code-segment-readable-bit x86))
;;   :hints (("Goal" :in-theory (enable set-rsp))))

;; (defthm code-segment-readable-bit-of-set-rbp
;;   (equal (code-segment-readable-bit (set-rbp rbp x86))
;;          (code-segment-readable-bit x86))
;;   :hints (("Goal" :in-theory (enable set-rbp))))

;; (defthm code-segment-readable-bit-of-write-byte-to-segment
;;   (equal (code-segment-readable-bit (write-byte-to-segment eff-addr seg-reg2 val x86))
;;          (code-segment-readable-bit x86))
;;   :hints (("Goal" :in-theory (enable write-byte-to-segment))))

;; (defthm code-segment-readable-bit-of-write-to-segment
;;   (equal (code-segment-readable-bit (write-to-segment n eff-addr seg-reg2 val x86))
;;          (code-segment-readable-bit x86))
;;   :hints (("Goal" :in-theory (enable write-to-segment))))

;; ;;;

;; (defthm code-segment-well-formedp-of-set-rax
;;   (equal (code-segment-well-formedp (set-rax rax x86))
;;          (code-segment-well-formedp x86))
;;   :hints (("Goal" :in-theory (enable set-rax))))

;; (defthm code-segment-well-formedp-of-set-rbx
;;   (equal (code-segment-well-formedp (set-rbx rbx x86))
;;          (code-segment-well-formedp x86))
;;   :hints (("Goal" :in-theory (enable set-rbx))))

;; (defthm code-segment-well-formedp-of-set-rcx
;;   (equal (code-segment-well-formedp (set-rcx rcx x86))
;;          (code-segment-well-formedp x86))
;;   :hints (("Goal" :in-theory (enable set-rcx))))

;; (defthm code-segment-well-formedp-of-set-rdx
;;   (equal (code-segment-well-formedp (set-rdx rdx x86))
;;          (code-segment-well-formedp x86))
;;   :hints (("Goal" :in-theory (enable set-rdx))))

;; (defthm code-segment-well-formedp-of-set-rsp
;;   (equal (code-segment-well-formedp (set-rsp rsp x86))
;;          (code-segment-well-formedp x86))
;;   :hints (("Goal" :in-theory (enable set-rsp))))

;; (defthm code-segment-well-formedp-of-set-rbp
;;   (equal (code-segment-well-formedp (set-rbp rbp x86))
;;          (code-segment-well-formedp x86))
;;   :hints (("Goal" :in-theory (enable set-rbp))))

;; (defthm code-segment-well-formedp-of-write-to-segment
;;   (equal (code-segment-well-formedp (write-to-segment n eff-addr seg-reg val x86))
;;          (code-segment-well-formedp x86))
;;   :hints (("Goal" :in-theory (enable code-segment-well-formedp
;;                                      code-and-stack-segments-separate
;;                                      32-bit-segment-size))))

;; ;;;

;; (defthm stack-segment-assumptions32-of-write-to-segment
;;   (equal (stack-segment-assumptions32 stack-slots-needed (write-to-segment n eff-addr seg-reg val x86))
;;          (stack-segment-assumptions32 stack-slots-needed x86))
;;   :hints (("Goal" :in-theory (e/d () (;; x86isa::rgfi-is-i64p
;;                                       ;; x86isa::seg-hidden-basei-is-n64p
;;                                       ;; x86isa::seg-hidden-limiti-is-n32p
;;                                       ;; x86isa::seg-hidden-attri-is-n16p
;;                                       ))))) ;bad forcing

;; ;;;

;; (defthm read-byte-from-segment-of-write-to-segment-diff-segments
;;   (implies (and (segments-separate seg-reg1 seg-reg2 x86)
;;                 (eff-addr-okp eff-addr1 seg-reg1 x86)
;;                 (eff-addrs-okp n2 eff-addr2 seg-reg2 x86)
;;                 (seg-regp seg-reg1)
;;                 (seg-regp seg-reg2)
;;                 (segment-is-32-bitsp seg-reg1 x86)
;;                 (segment-is-32-bitsp seg-reg2 x86)
;;                 (x86p x86)
;;                 (not (64-bit-modep x86))
;;                 (natp eff-addr1)
;;                 (natp eff-addr2)
;;                 (well-formed-32-bit-segmentp seg-reg1 x86)
;;                 (well-formed-32-bit-segmentp seg-reg2 x86))
;;            (equal (read-byte-from-segment eff-addr1 seg-reg1 (write-to-segment n2 eff-addr2 seg-reg2 val x86))
;;                   (read-byte-from-segment eff-addr1 seg-reg1 x86)))
;;   :hints (("Goal" :in-theory (enable write-to-segment
;;                                      segment-min-eff-addr32
;;                                      segment-max-eff-addr32))))

;; (defthm read-byte-list-from-segment-of-write-to-segment-diff-segments
;;   (implies (and (segments-separate seg-reg1 seg-reg2 x86)
;;                 (eff-addrs-okp n1 eff-addr1 seg-reg1 x86)
;;                 (eff-addrs-okp n2 eff-addr2 seg-reg2 x86)
;;                 (seg-regp seg-reg1)
;;                 (seg-regp seg-reg2)
;;                 (segment-is-32-bitsp seg-reg1 x86)
;;                 (segment-is-32-bitsp seg-reg2 x86)
;;                 (< n1 (expt 2 32))
;;                 (natp eff-addr1)
;;                 (natp eff-addr2)
;;                 (natp n2)
;;                 (not (64-bit-modep x86))
;; ;                (not (equal seg-reg1 seg-reg2))
;;                 ;; (< (+ -1 n1 eff-addr1) (32-bit-segment-size seg-reg1 x86))
;;                 ;; (< (+ -1 n2 eff-addr2) (32-bit-segment-size seg-reg2 x86))
;;                 (well-formed-32-bit-segmentp seg-reg1 x86)
;;                 (well-formed-32-bit-segmentp seg-reg2 x86)
;;                 (x86p x86))
;;            (equal (read-byte-list-from-segment n1 eff-addr1 seg-reg1 (write-to-segment n2 eff-addr2 seg-reg2 val x86))
;;                   (read-byte-list-from-segment n1 eff-addr1 seg-reg1 x86)))
;;   :hints (("Goal" :expand (;(write-to-segment n eff-addr seg-reg2 val x86)
;;                            ;;(READ-BYTE-FROM-SEGMENT EFF-ADDR1 SEG-REG1 X86)
;;                            )
;;            :induct (READ-BYTE-LIST-FROM-SEGMENT N1 EFF-ADDR1 SEG-REG1 X86)
;;            :in-theory (e/d (read-byte-list-from-segment
;;                               write-to-segment
;;                               write-to-segment-of-write-byte-to-segment)
;;                            (READ-BYTE-FROM-SEGMENT)))))

;; (defthm code-segment-assumptions32-for-code-of-write-to-segment
;;   (implies (and (segments-separate *cs* seg-reg x86)
;;                 (seg-regp seg-reg)
;;                 (segment-is-32-bitsp seg-reg x86)
;;                 (< (len code) 4294967296)
;;                 (natp eff-addr)
;;                 (natp n)
;;                 (<= (len code) (32-bit-segment-size *cs* x86))
;;                 (< 0 (32-bit-segment-size seg-reg x86)) ;drop?
;;                 ;(< (+ -1 n eff-addr) (32-bit-segment-size seg-reg x86)) ;gen
;;                 (eff-addrs-okp n eff-addr seg-reg x86)
;;                 (code-segment-well-formedp x86)
;;                 ;(well-formed-32-bit-segmentp *cs* x86)
;;                 (well-formed-32-bit-segmentp seg-reg x86)
;;                 (not (64-bit-modep x86))
;;                 (natp offset)
;;                 (x86p x86))
;;            (equal (code-segment-assumptions32-for-code code offset (write-to-segment n eff-addr seg-reg val x86))
;;                   (code-segment-assumptions32-for-code code offset x86)))
;;   :hints (("Goal" :in-theory (enable code-segment-assumptions32-for-code
;;                                      code-and-stack-segments-separate 32-bit-segment-size))))

;; (defthm read-from-segment-of-write-to-segment-diff-segments
;;   (implies (and (segments-separate seg-reg1 seg-reg2 x86)
;;                 (eff-addrs-okp n1 eff-addr1 seg-reg1 x86)
;;                 (eff-addrs-okp n2 eff-addr2 seg-reg2 x86)
;;                 (seg-regp seg-reg1)
;;                 (seg-regp seg-reg2)
;;                 (segment-is-32-bitsp seg-reg1 x86)
;;                 (segment-is-32-bitsp seg-reg2 x86)
;;                 (x86p x86)
;;                 (not (64-bit-modep x86))
;;                 (natp eff-addr1)
;;                 (natp eff-addr2)
;;                 (well-formed-32-bit-segmentp seg-reg1 x86)
;;                 (well-formed-32-bit-segmentp seg-reg2 x86))
;;            (equal (read-from-segment n1 eff-addr1 seg-reg1 (write-to-segment n2 eff-addr2 seg-reg2 val x86))
;;                   (read-from-segment n1 eff-addr1 seg-reg1 x86)))
;;   :hints (("Goal" :in-theory (enable write-to-segment
;;                                      segment-min-eff-addr32
;;                                      segment-max-eff-addr32))))


;; ;move?
;; (defthm write-to-segment-of-write-byte-to-segment-included
;;   (implies (and (integerp eff-addr1)
;;                 (integerp eff-addr2)
;;                 (<= eff-addr1 eff-addr2)
;;                 (< eff-addr2 (+ eff-addr1 n)) ;not a cyclic range...
;;                 (unsigned-byte-p 32 n)
;;                 (x86p x86))
;;            (equal (write-to-segment n eff-addr1 seg-reg val1 (write-byte-to-segment eff-addr2 seg-reg val2 x86))
;;                   (write-to-segment n eff-addr1 seg-reg val1 x86)))
;;   :hints (
;;           ("Goal" :induct (write-to-segment n eff-addr1 seg-reg val1 x86)
;;            :in-theory (e/d (sep-eff-addr-ranges-swap
;;                             write-to-segment
;;                             unsigned-byte-p)
;;                            (sep-eff-addr-ranges
;;                             acl2::bvcat-equal-rewrite-alt
;;
;;                             acl2::bvcat-equal-rewrite)))))

;; (defthm write-to-segment-of-write-to-segment-included
;;   (implies (and (integerp eff-addr1)
;;                 (integerp eff-addr2)
;;                 (<= eff-addr1 eff-addr2)
;;                 (<= (+ eff-addr2 n2) (+ eff-addr1 n1)) ;not a cyclic range...
;;                 (unsigned-byte-p 32 n1)
;;                 (unsigned-byte-p 32 n2)
;;                 (x86p x86))
;;            (equal (write-to-segment n1 eff-addr1 seg-reg val1 (write-to-segment n2 eff-addr2 seg-reg val2 x86))
;;                   (write-to-segment n1 eff-addr1 seg-reg val1 x86)))
;;   :hints (("Goal" :induct (write-to-segment n2 eff-addr2 seg-reg val2 x86)
;;            :in-theory (e/d (sep-eff-addr-ranges-swap
;;                             write-to-segment
;;                             unsigned-byte-p)
;;                            (sep-eff-addr-ranges
;;                             acl2::bvcat-equal-rewrite-alt
;;
;;                             acl2::bvcat-equal-rewrite)))))

;; ;;;

;; (defthm read-stack-dword-of-set-rip
;;   (equal (read-stack-dword eff-addr (set-rip val x86))
;;          (read-stack-dword eff-addr x86))
;;   :hints (("Goal" :in-theory (enable set-rip))))

;; (defthm read-stack-dword-of-set-rax
;;   (equal (read-stack-dword eff-addr (set-rax val x86))
;;          (read-stack-dword eff-addr x86))
;;   :hints (("Goal" :in-theory (enable set-rax))))

;; (defthm read-stack-dword-of-set-rbx
;;   (equal (read-stack-dword eff-addr (set-rbx val x86))
;;          (read-stack-dword eff-addr x86))
;;   :hints (("Goal" :in-theory (enable set-rbx))))

;; (defthm read-stack-dword-of-set-rcx
;;   (equal (read-stack-dword eff-addr (set-rcx val x86))
;;          (read-stack-dword eff-addr x86))
;;   :hints (("Goal" :in-theory (enable set-rcx))))

;; (defthm read-stack-dword-of-set-rdx
;;   (equal (read-stack-dword eff-addr (set-rdx val x86))
;;          (read-stack-dword eff-addr x86))
;;   :hints (("Goal" :in-theory (enable set-rdx))))

;; (defthm read-stack-dword-of-set-rsp
;;   (equal (read-stack-dword eff-addr (set-rsp val x86))
;;          (read-stack-dword eff-addr x86))
;;   :hints (("Goal" :in-theory (enable set-rsp))))

;; (defthm read-stack-dword-of-set-rbp
;;   (equal (read-stack-dword eff-addr (set-rbp val x86))
;;          (read-stack-dword eff-addr x86))
;;   :hints (("Goal" :in-theory (enable set-rbp))))

;; (local (in-theory (disable read-stack-dword-intro)))

;; (defthm read-stack-dword-of-write-to-segment-diff-segments
;;   (implies (and (segments-separate *ss* seg-reg2 x86)
;;                 (eff-addrs-okp 4 eff-addr1 *ss* x86)
;;                 (eff-addrs-okp n2 eff-addr2 seg-reg2 x86)
;;                 (seg-regp seg-reg2)
;;                 (segment-is-32-bitsp *ss* x86)
;;                 (segment-is-32-bitsp seg-reg2 x86)
;;                 (x86p x86)
;;                 (not (64-bit-modep x86))
;;                 (natp eff-addr1)
;;                 (natp eff-addr2)
;;                 (well-formed-32-bit-segmentp *ss* x86)
;;                 (well-formed-32-bit-segmentp seg-reg2 x86))
;;            (equal (read-stack-dword eff-addr1 (write-to-segment n2 eff-addr2 seg-reg2 val x86))
;;                   (read-stack-dword eff-addr1 x86)))
;;   :hints (("Goal" :in-theory (enable read-stack-dword))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm ctri-of-set-rip (equal (ctri i (set-rip rip x86)) (ctri i x86)) :hints (("Goal" :in-theory (enable set-rip))))
(defthm ctri-of-set-rax (equal (ctri i (set-rax val x86)) (ctri i x86)) :hints (("Goal" :in-theory (enable set-rax))))
(defthm ctri-of-set-rbx (equal (ctri i (set-rbx val x86)) (ctri i x86)) :hints (("Goal" :in-theory (enable set-rbx))))
(defthm ctri-of-set-rcx (equal (ctri i (set-rcx val x86)) (ctri i x86)) :hints (("Goal" :in-theory (enable set-rcx))))
(defthm ctri-of-set-rdx (equal (ctri i (set-rdx val x86)) (ctri i x86)) :hints (("Goal" :in-theory (enable set-rdx))))
(defthm ctri-of-set-rsi (equal (ctri i (set-rsi val x86)) (ctri i x86)) :hints (("Goal" :in-theory (enable set-rsi))))
(defthm ctri-of-set-rdi (equal (ctri i (set-rdi val x86)) (ctri i x86)) :hints (("Goal" :in-theory (enable set-rdi))))
(defthm ctri-of-set-r8 (equal (ctri i (set-r8 val x86)) (ctri i x86)) :hints (("Goal" :in-theory (enable set-r8))))
(defthm ctri-of-set-r9 (equal (ctri i (set-r9 val x86)) (ctri i x86)) :hints (("Goal" :in-theory (enable set-r9))))
(defthm ctri-of-set-r10 (equal (ctri i (set-r10 val x86)) (ctri i x86)) :hints (("Goal" :in-theory (enable set-r10))))
(defthm ctri-of-set-r11 (equal (ctri i (set-r11 val x86)) (ctri i x86)) :hints (("Goal" :in-theory (enable set-r11))))
(defthm ctri-of-set-r12 (equal (ctri i (set-r12 val x86)) (ctri i x86)) :hints (("Goal" :in-theory (enable set-r12))))
(defthm ctri-of-set-r13 (equal (ctri i (set-r13 val x86)) (ctri i x86)) :hints (("Goal" :in-theory (enable set-r13))))
(defthm ctri-of-set-r14 (equal (ctri i (set-r14 val x86)) (ctri i x86)) :hints (("Goal" :in-theory (enable set-r14))))
(defthm ctri-of-set-r15 (equal (ctri i (set-r15 val x86)) (ctri i x86)) :hints (("Goal" :in-theory (enable set-r15))))
(defthm ctri-of-set-rsp (equal (ctri i (set-rsp val x86)) (ctri i x86)) :hints (("Goal" :in-theory (enable set-rsp))))
(defthm ctri-of-set-rbp (equal (ctri i (set-rbp val x86)) (ctri i x86)) :hints (("Goal" :in-theory (enable set-rbp))))

(defthm ctri-of-write-byte (equal (ctri i (write-byte base-addr byte x86)) (ctri i x86)) :hints (("Goal" :in-theory (enable write-byte))))
(defthm ctri-of-write (equal (ctri i (write n base-addr val x86)) (ctri i x86)) :hints (("Goal" :in-theory (enable write))))
(defthm ctri-of-write-bytes (implies (ctri i x86) (ctri i (write-bytes base-addr vals x86))) :hints (("Goal" :in-theory (enable write-bytes))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm msri-of-set-rip (equal (msri i (set-rip rip x86)) (msri i x86)) :hints (("Goal" :in-theory (enable set-rip))))
(defthm msri-of-set-rax (equal (msri i (set-rax val x86)) (msri i x86)) :hints (("Goal" :in-theory (enable set-rax))))
(defthm msri-of-set-rbx (equal (msri i (set-rbx val x86)) (msri i x86)) :hints (("Goal" :in-theory (enable set-rbx))))
(defthm msri-of-set-rcx (equal (msri i (set-rcx val x86)) (msri i x86)) :hints (("Goal" :in-theory (enable set-rcx))))
(defthm msri-of-set-rdx (equal (msri i (set-rdx val x86)) (msri i x86)) :hints (("Goal" :in-theory (enable set-rdx))))
(defthm msri-of-set-rsi (equal (msri i (set-rsi val x86)) (msri i x86)) :hints (("Goal" :in-theory (enable set-rsi))))
(defthm msri-of-set-rdi (equal (msri i (set-rdi val x86)) (msri i x86)) :hints (("Goal" :in-theory (enable set-rdi))))
(defthm msri-of-set-r8 (equal (msri i (set-r8 val x86)) (msri i x86)) :hints (("Goal" :in-theory (enable set-r8))))
(defthm msri-of-set-r9 (equal (msri i (set-r9 val x86)) (msri i x86)) :hints (("Goal" :in-theory (enable set-r9))))
(defthm msri-of-set-r10 (equal (msri i (set-r10 val x86)) (msri i x86)) :hints (("Goal" :in-theory (enable set-r10))))
(defthm msri-of-set-r11 (equal (msri i (set-r11 val x86)) (msri i x86)) :hints (("Goal" :in-theory (enable set-r11))))
(defthm msri-of-set-r12 (equal (msri i (set-r12 val x86)) (msri i x86)) :hints (("Goal" :in-theory (enable set-r12))))
(defthm msri-of-set-r13 (equal (msri i (set-r13 val x86)) (msri i x86)) :hints (("Goal" :in-theory (enable set-r13))))
(defthm msri-of-set-r14 (equal (msri i (set-r14 val x86)) (msri i x86)) :hints (("Goal" :in-theory (enable set-r14))))
(defthm msri-of-set-r15 (equal (msri i (set-r15 val x86)) (msri i x86)) :hints (("Goal" :in-theory (enable set-r15))))
(defthm msri-of-set-rsp (equal (msri i (set-rsp val x86)) (msri i x86)) :hints (("Goal" :in-theory (enable set-rsp))))
(defthm msri-of-set-rbp (equal (msri i (set-rbp val x86)) (msri i x86)) :hints (("Goal" :in-theory (enable set-rbp))))

(defthm msri-of-write-byte (equal (msri i (write-byte base-addr byte x86)) (msri i x86)) :hints (("Goal" :in-theory (enable write-byte))))
(defthm msri-of-write (equal (msri i (write n base-addr val x86)) (msri i x86)) :hints (("Goal" :in-theory (enable write))))
(defthm msri-of-write-bytes (implies (msri i x86) (msri i (write-bytes base-addr vals x86))) :hints (("Goal" :in-theory (enable write-bytes))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; todo: finish this:

(defthm mv-nth-0-of-rml-size-when-app-view
  (implies (and (not (equal :mem fld))
                (not (equal :app-view fld))
                (app-view x86) ; why?
                )
           (equal (mv-nth 0 (rml-size nbytes addr r-x (xw fld index val x86)))
                  (mv-nth 0 (rml-size nbytes addr r-x x86))))
  :hints (("Goal" :in-theory (enable rml-size
                                     rb ;todo
                                     rb-1
                                     rml128
                                     rml48
                                     rml80
                                     ))))

(defthm mv-nth-1-of-rml-size-when-app-view
  (implies (and (not (equal :mem fld))
                (not (equal :app-view fld))
                (app-view x86) ; why?
                )
           (equal (mv-nth 1 (rml-size nbytes addr r-x (xw fld index val x86)))
                  (mv-nth 1 (rml-size nbytes addr r-x x86))))
  :hints (("Goal" :in-theory (enable rml-size
                                     rb ;todo
                                     rb-1
                                     rml128
                                     rml48
                                     rml80
                                     rb-1))))

(encapsulate ()
  (local (in-theory (enable rml80
                            rml48
                            rml128
                            rme-size$inline)))

  (local (in-theory (disable ea-to-la$inline)))

  (defthm mv-nth-0-of-rme-size-of-set-rip (implies (app-view x86) (equal (mv-nth 0 (rme-size p n e s r c (set-rip rip x86))) (mv-nth 0 (rme-size p n e s r c x86)))) :hints (("Goal" :in-theory (enable set-rip))))
  (defthm mv-nth-0-of-rme-size-of-set-rax (implies (app-view x86) (equal (mv-nth 0 (rme-size p n e s r c (set-rax val x86))) (mv-nth 0 (rme-size p n e s r c x86)))) :hints (("Goal" :in-theory (enable set-rax))))
  (defthm mv-nth-0-of-rme-size-of-set-rbx (implies (app-view x86) (equal (mv-nth 0 (rme-size p n e s r c (set-rbx val x86))) (mv-nth 0 (rme-size p n e s r c x86)))) :hints (("Goal" :in-theory (enable set-rbx))))
  (defthm mv-nth-0-of-rme-size-of-set-rcx (implies (app-view x86) (equal (mv-nth 0 (rme-size p n e s r c (set-rcx val x86))) (mv-nth 0 (rme-size p n e s r c x86)))) :hints (("Goal" :in-theory (enable set-rcx))))
  (defthm mv-nth-0-of-rme-size-of-set-rdx (implies (app-view x86) (equal (mv-nth 0 (rme-size p n e s r c (set-rdx val x86))) (mv-nth 0 (rme-size p n e s r c x86)))) :hints (("Goal" :in-theory (enable set-rdx))))
  (defthm mv-nth-0-of-rme-size-of-set-rsi (implies (app-view x86) (equal (mv-nth 0 (rme-size p n e s r c (set-rsi val x86))) (mv-nth 0 (rme-size p n e s r c x86)))) :hints (("Goal" :in-theory (enable set-rsi))))
  (defthm mv-nth-0-of-rme-size-of-set-rdi (implies (app-view x86) (equal (mv-nth 0 (rme-size p n e s r c (set-rdi val x86))) (mv-nth 0 (rme-size p n e s r c x86)))) :hints (("Goal" :in-theory (enable set-rdi))))
  (defthm mv-nth-0-of-rme-size-of-set-r8 (implies (app-view x86) (equal (mv-nth 0 (rme-size p n e s r c (set-r8 val x86))) (mv-nth 0 (rme-size p n e s r c x86)))) :hints (("Goal" :in-theory (enable set-r8))))
  (defthm mv-nth-0-of-rme-size-of-set-r9 (implies (app-view x86) (equal (mv-nth 0 (rme-size p n e s r c (set-r9 val x86))) (mv-nth 0 (rme-size p n e s r c x86)))) :hints (("Goal" :in-theory (enable set-r9))))
  (defthm mv-nth-0-of-rme-size-of-set-r10 (implies (app-view x86) (equal (mv-nth 0 (rme-size p n e s r c (set-r10 val x86))) (mv-nth 0 (rme-size p n e s r c x86)))) :hints (("Goal" :in-theory (enable set-r10))))
  (defthm mv-nth-0-of-rme-size-of-set-r11 (implies (app-view x86) (equal (mv-nth 0 (rme-size p n e s r c (set-r11 val x86))) (mv-nth 0 (rme-size p n e s r c x86)))) :hints (("Goal" :in-theory (enable set-r11))))
  (defthm mv-nth-0-of-rme-size-of-set-r12 (implies (app-view x86) (equal (mv-nth 0 (rme-size p n e s r c (set-r12 val x86))) (mv-nth 0 (rme-size p n e s r c x86)))) :hints (("Goal" :in-theory (enable set-r12))))
  (defthm mv-nth-0-of-rme-size-of-set-r13 (implies (app-view x86) (equal (mv-nth 0 (rme-size p n e s r c (set-r13 val x86))) (mv-nth 0 (rme-size p n e s r c x86)))) :hints (("Goal" :in-theory (enable set-r13))))
  (defthm mv-nth-0-of-rme-size-of-set-r14 (implies (app-view x86) (equal (mv-nth 0 (rme-size p n e s r c (set-r14 val x86))) (mv-nth 0 (rme-size p n e s r c x86)))) :hints (("Goal" :in-theory (enable set-r14))))
  (defthm mv-nth-0-of-rme-size-of-set-r15 (implies (app-view x86) (equal (mv-nth 0 (rme-size p n e s r c (set-r15 val x86))) (mv-nth 0 (rme-size p n e s r c x86)))) :hints (("Goal" :in-theory (enable set-r15))))
  (defthm mv-nth-0-of-rme-size-of-set-rsp (implies (app-view x86) (equal (mv-nth 0 (rme-size p n e s r c (set-rsp val x86))) (mv-nth 0 (rme-size p n e s r c x86)))) :hints (("Goal" :in-theory (enable set-rsp))))
  (defthm mv-nth-0-of-rme-size-of-set-rbp (implies (app-view x86) (equal (mv-nth 0 (rme-size p n e s r c (set-rbp val x86))) (mv-nth 0 (rme-size p n e s r c x86)))) :hints (("Goal" :in-theory (enable set-rbp))))
  (defthm mv-nth-0-of-rme-size-of-set-undef (implies (app-view x86) (equal (mv-nth 0 (rme-size p n e s r c (set-undef val x86))) (mv-nth 0 (rme-size p n e s r c x86)))) :hints (("Goal" :in-theory (enable set-undef))))
  (defthm mv-nth-0-of-rme-size-of-set-mxcsr (implies (app-view x86) (equal (mv-nth 0 (rme-size p n e s r c (set-mxcsr val x86))) (mv-nth 0 (rme-size p n e s r c x86)))) :hints (("Goal" :in-theory (enable set-mxcsr))))
;;  (defthm mv-nth-0-of-rme-size-of-set-ms (implies (app-view x86) (equal (mv-nth 0 (rme-size p n e s r c (set-ms val x86))) (mv-nth 0 (rme-size p n e s r c x86)))) :hints (("Goal" :in-theory (enable set-ms))))

  (defthm mv-nth-1-of-rme-size-of-set-rip (implies (app-view x86) (equal (mv-nth 1 (rme-size p n e s r c (set-rip rip x86))) (mv-nth 1 (rme-size p n e s r c x86)))) :hints (("Goal" :in-theory (enable set-rip))))
  (defthm mv-nth-1-of-rme-size-of-set-rax (implies (app-view x86) (equal (mv-nth 1 (rme-size p n e s r c (set-rax val x86))) (mv-nth 1 (rme-size p n e s r c x86)))) :hints (("Goal" :in-theory (enable set-rax))))
  (defthm mv-nth-1-of-rme-size-of-set-rbx (implies (app-view x86) (equal (mv-nth 1 (rme-size p n e s r c (set-rbx val x86))) (mv-nth 1 (rme-size p n e s r c x86)))) :hints (("Goal" :in-theory (enable set-rbx))))
  (defthm mv-nth-1-of-rme-size-of-set-rcx (implies (app-view x86) (equal (mv-nth 1 (rme-size p n e s r c (set-rcx val x86))) (mv-nth 1 (rme-size p n e s r c x86)))) :hints (("Goal" :in-theory (enable set-rcx))))
  (defthm mv-nth-1-of-rme-size-of-set-rdx (implies (app-view x86) (equal (mv-nth 1 (rme-size p n e s r c (set-rdx val x86))) (mv-nth 1 (rme-size p n e s r c x86)))) :hints (("Goal" :in-theory (enable set-rdx))))
  (defthm mv-nth-1-of-rme-size-of-set-rsi (implies (app-view x86) (equal (mv-nth 1 (rme-size p n e s r c (set-rsi val x86))) (mv-nth 1 (rme-size p n e s r c x86)))) :hints (("Goal" :in-theory (enable set-rsi))))
  (defthm mv-nth-1-of-rme-size-of-set-rdi (implies (app-view x86) (equal (mv-nth 1 (rme-size p n e s r c (set-rdi val x86))) (mv-nth 1 (rme-size p n e s r c x86)))) :hints (("Goal" :in-theory (enable set-rdi))))
  (defthm mv-nth-1-of-rme-size-of-set-r8 (implies (app-view x86) (equal (mv-nth 1 (rme-size p n e s r c (set-r8 val x86))) (mv-nth 1 (rme-size p n e s r c x86)))) :hints (("Goal" :in-theory (enable set-r8))))
  (defthm mv-nth-1-of-rme-size-of-set-r9 (implies (app-view x86) (equal (mv-nth 1 (rme-size p n e s r c (set-r9 val x86))) (mv-nth 1 (rme-size p n e s r c x86)))) :hints (("Goal" :in-theory (enable set-r9))))
  (defthm mv-nth-1-of-rme-size-of-set-r10 (implies (app-view x86) (equal (mv-nth 1 (rme-size p n e s r c (set-r10 val x86))) (mv-nth 1 (rme-size p n e s r c x86)))) :hints (("Goal" :in-theory (enable set-r10))))
  (defthm mv-nth-1-of-rme-size-of-set-r11 (implies (app-view x86) (equal (mv-nth 1 (rme-size p n e s r c (set-r11 val x86))) (mv-nth 1 (rme-size p n e s r c x86)))) :hints (("Goal" :in-theory (enable set-r11))))
  (defthm mv-nth-1-of-rme-size-of-set-r12 (implies (app-view x86) (equal (mv-nth 1 (rme-size p n e s r c (set-r12 val x86))) (mv-nth 1 (rme-size p n e s r c x86)))) :hints (("Goal" :in-theory (enable set-r12))))
  (defthm mv-nth-1-of-rme-size-of-set-r13 (implies (app-view x86) (equal (mv-nth 1 (rme-size p n e s r c (set-r13 val x86))) (mv-nth 1 (rme-size p n e s r c x86)))) :hints (("Goal" :in-theory (enable set-r13))))
  (defthm mv-nth-1-of-rme-size-of-set-r14 (implies (app-view x86) (equal (mv-nth 1 (rme-size p n e s r c (set-r14 val x86))) (mv-nth 1 (rme-size p n e s r c x86)))) :hints (("Goal" :in-theory (enable set-r14))))
  (defthm mv-nth-1-of-rme-size-of-set-r15 (implies (app-view x86) (equal (mv-nth 1 (rme-size p n e s r c (set-r15 val x86))) (mv-nth 1 (rme-size p n e s r c x86)))) :hints (("Goal" :in-theory (enable set-r15))))
  (defthm mv-nth-1-of-rme-size-of-set-rsp (implies (app-view x86) (equal (mv-nth 1 (rme-size p n e s r c (set-rsp val x86))) (mv-nth 1 (rme-size p n e s r c x86)))) :hints (("Goal" :in-theory (enable set-rsp))))
  (defthm mv-nth-1-of-rme-size-of-set-rbp (implies (app-view x86) (equal (mv-nth 1 (rme-size p n e s r c (set-rbp val x86))) (mv-nth 1 (rme-size p n e s r c x86)))) :hints (("Goal" :in-theory (enable set-rbp))))
  (defthm mv-nth-1-of-rme-size-of-set-undef (implies (app-view x86) (equal (mv-nth 1 (rme-size p n e s r c (set-undef val x86))) (mv-nth 1 (rme-size p n e s r c x86)))) :hints (("Goal" :in-theory (enable set-undef))))
  (defthm mv-nth-1-of-rme-size-of-set-mxcsr (implies (app-view x86) (equal (mv-nth 1 (rme-size p n e s r c (set-mxcsr val x86))) (mv-nth 1 (rme-size p n e s r c x86)))) :hints (("Goal" :in-theory (enable set-mxcsr))))
;;  (defthm mv-nth-1-of-rme-size-of-set-ms (implies (app-view x86) (equal (mv-nth 1 (rme-size p n e s r c (set-ms val x86))) (mv-nth 1 (rme-size p n e s r c x86)))) :hints (("Goal" :in-theory (enable set-ms))))
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm segment-base-and-bounds-of-set-rip
  (equal (segment-base-and-bounds proc-mode seg-reg (set-rip rip x86))
         (segment-base-and-bounds proc-mode seg-reg x86))
  :hints (("Goal" :in-theory (enable set-rip))))

(defthm segment-base-and-bounds-of-set-rsp
  (equal (segment-base-and-bounds proc-mode seg-reg (set-rsp rsp x86))
         (segment-base-and-bounds proc-mode seg-reg x86))
  :hints (("Goal" :in-theory (enable set-rsp))))

(defthm segment-base-and-bounds-of-set-rbp
  (equal (segment-base-and-bounds proc-mode seg-reg (set-rbp rbp x86))
         (segment-base-and-bounds proc-mode seg-reg x86))
  :hints (("Goal" :in-theory (enable set-rbp))))

(defthm segment-base-and-bounds-of-set-rax
  (equal (segment-base-and-bounds proc-mode seg-reg (set-rax rax x86))
         (segment-base-and-bounds proc-mode seg-reg x86))
  :hints (("Goal" :in-theory (enable set-rax))))

(defthm segment-base-and-bounds-of-set-rbx
  (equal (segment-base-and-bounds proc-mode seg-reg (set-rbx rbx x86))
         (segment-base-and-bounds proc-mode seg-reg x86))
  :hints (("Goal" :in-theory (enable set-rbx))))

(defthm segment-base-and-bounds-of-set-rcx
  (equal (segment-base-and-bounds proc-mode seg-reg (set-rcx rcx x86))
         (segment-base-and-bounds proc-mode seg-reg x86))
  :hints (("Goal" :in-theory (enable set-rcx))))

(defthm segment-base-and-bounds-of-set-rdx
  (equal (segment-base-and-bounds proc-mode seg-reg (set-rdx rdx x86))
         (segment-base-and-bounds proc-mode seg-reg x86))
  :hints (("Goal" :in-theory (enable set-rdx))))

;todo: more!

(defthm segment-base-and-bounds-of-set-rsi
  (equal (segment-base-and-bounds proc-mode seg-reg (set-rsi rsi x86))
         (segment-base-and-bounds proc-mode seg-reg x86))
  :hints (("Goal" :in-theory (enable set-rsi))))

(defthm segment-base-and-bounds-of-set-rdi
  (equal (segment-base-and-bounds proc-mode seg-reg (set-rdi rdi x86))
         (segment-base-and-bounds proc-mode seg-reg x86))
  :hints (("Goal" :in-theory (enable set-rdi))))

(defthm segment-base-and-bounds-of-set-r8 (equal (segment-base-and-bounds proc-mode seg-reg (set-r8 r8 x86)) (segment-base-and-bounds proc-mode seg-reg x86)) :hints (("Goal" :in-theory (enable set-r8))))
(defthm segment-base-and-bounds-of-set-r9 (equal (segment-base-and-bounds proc-mode seg-reg (set-r9 r9 x86)) (segment-base-and-bounds proc-mode seg-reg x86)) :hints (("Goal" :in-theory (enable set-r9))))
(defthm segment-base-and-bounds-of-set-r10 (equal (segment-base-and-bounds proc-mode seg-reg (set-r10 r10 x86)) (segment-base-and-bounds proc-mode seg-reg x86)) :hints (("Goal" :in-theory (enable set-r10))))
(defthm segment-base-and-bounds-of-set-r11 (equal (segment-base-and-bounds proc-mode seg-reg (set-r11 r11 x86)) (segment-base-and-bounds proc-mode seg-reg x86)) :hints (("Goal" :in-theory (enable set-r11))))
(defthm segment-base-and-bounds-of-set-r12 (equal (segment-base-and-bounds proc-mode seg-reg (set-r12 r12 x86)) (segment-base-and-bounds proc-mode seg-reg x86)) :hints (("Goal" :in-theory (enable set-r12))))
(defthm segment-base-and-bounds-of-set-r13 (equal (segment-base-and-bounds proc-mode seg-reg (set-r13 r13 x86)) (segment-base-and-bounds proc-mode seg-reg x86)) :hints (("Goal" :in-theory (enable set-r13))))
(defthm segment-base-and-bounds-of-set-r14 (equal (segment-base-and-bounds proc-mode seg-reg (set-r14 r14 x86)) (segment-base-and-bounds proc-mode seg-reg x86)) :hints (("Goal" :in-theory (enable set-r14))))
(defthm segment-base-and-bounds-of-set-r15 (equal (segment-base-and-bounds proc-mode seg-reg (set-r15 r15 x86)) (segment-base-and-bounds proc-mode seg-reg x86)) :hints (("Goal" :in-theory (enable set-r15))))

(defthm segment-base-and-bounds-of-write-byte
  (equal (segment-base-and-bounds proc-mode seg-reg (write-byte base-addr byte x86))
         (segment-base-and-bounds proc-mode seg-reg x86))
  :hints (("Goal" :in-theory (enable write-byte))))

(defthm segment-base-and-bounds-of-write
  (equal (segment-base-and-bounds proc-mode seg-reg (write n base-addr val x86))
         (segment-base-and-bounds proc-mode seg-reg x86))
  :hints (("Goal" :in-theory (enable write))))

(defthm segment-base-and-bounds-of-write-bytes
  (equal (segment-base-and-bounds proc-mode seg-reg (write-bytes base-addr vals x86))
         (segment-base-and-bounds proc-mode seg-reg x86))
  :hints (("Goal" :in-theory (enable write-bytes))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;todo: more like this!
(defthm mv-nth-0-of-get-prefixes-of-set-rip
  (equal (mv-nth 0 (get-prefixes proc-mode start-rip prefixes rex-byte cnt (set-rip rip x86)))
         (mv-nth 0 (get-prefixes proc-mode start-rip prefixes rex-byte cnt x86)))
  :hints (("Goal" :in-theory (enable set-rip))))

(defthm mv-nth-0-of-get-prefixes-of-set-rax
  (equal (mv-nth 0 (get-prefixes proc-mode start-rip prefixes rex-byte cnt (set-rax rax x86)))
         (mv-nth 0 (get-prefixes proc-mode start-rip prefixes rex-byte cnt x86)))
  :hints (("Goal" :in-theory (enable set-rax))))

(defthm mv-nth-0-of-get-prefixes-of-set-rdx
  (equal (mv-nth 0 (get-prefixes proc-mode start-rip prefixes rex-byte cnt (set-rdx rdx x86)))
         (mv-nth 0 (get-prefixes proc-mode start-rip prefixes rex-byte cnt x86)))
  :hints (("Goal" :in-theory (enable set-rdx))))

(defthm mv-nth-0-of-get-prefixes-of-set-rsi
  (equal (mv-nth 0 (get-prefixes proc-mode start-rip prefixes rex-byte cnt (set-rsi rsi x86)))
         (mv-nth 0 (get-prefixes proc-mode start-rip prefixes rex-byte cnt x86)))
  :hints (("Goal" :in-theory (enable set-rsi))))

(defthm mv-nth-0-of-get-prefixes-of-set-rdi
  (equal (mv-nth 0 (get-prefixes proc-mode start-rip prefixes rex-byte cnt (set-rdi rdi x86)))
         (mv-nth 0 (get-prefixes proc-mode start-rip prefixes rex-byte cnt x86)))
  :hints (("Goal" :in-theory (enable set-rdi))))

(defthm mv-nth-0-of-get-prefixes-of-set-rsp
  (equal (mv-nth 0 (get-prefixes proc-mode start-rip prefixes rex-byte cnt (set-rsp rsp x86)))
         (mv-nth 0 (get-prefixes proc-mode start-rip prefixes rex-byte cnt x86)))
  :hints (("Goal" :in-theory (enable set-rsp))))

(defthm mv-nth-0-of-get-prefixes-of-set-rbp
  (equal (mv-nth 0 (get-prefixes proc-mode start-rip prefixes rex-byte cnt (set-rbp rbp x86)))
         (mv-nth 0 (get-prefixes proc-mode start-rip prefixes rex-byte cnt x86)))
  :hints (("Goal" :in-theory (enable set-rbp))))

;;;

;todo: more like this!
(defthm mv-nth-1-of-get-prefixes-of-set-rip
  (equal (mv-nth 1 (get-prefixes proc-mode start-rip prefixes rex-byte cnt (set-rip rip x86)))
         (mv-nth 1 (get-prefixes proc-mode start-rip prefixes rex-byte cnt x86)))
  :hints (("Goal" :in-theory (enable set-rip))))

(defthm mv-nth-1-of-get-prefixes-of-set-rax
  (equal (mv-nth 1 (get-prefixes proc-mode start-rip prefixes rex-byte cnt (set-rax rax x86)))
         (mv-nth 1 (get-prefixes proc-mode start-rip prefixes rex-byte cnt x86)))
  :hints (("Goal" :in-theory (enable set-rax))))

(defthm mv-nth-1-of-get-prefixes-of-set-rdx
  (equal (mv-nth 1 (get-prefixes proc-mode start-rip prefixes rex-byte cnt (set-rdx rdx x86)))
         (mv-nth 1 (get-prefixes proc-mode start-rip prefixes rex-byte cnt x86)))
  :hints (("Goal" :in-theory (enable set-rdx))))

(defthm mv-nth-1-of-get-prefixes-of-set-rsi
  (equal (mv-nth 1 (get-prefixes proc-mode start-rip prefixes rex-byte cnt (set-rsi rsi x86)))
         (mv-nth 1 (get-prefixes proc-mode start-rip prefixes rex-byte cnt x86)))
  :hints (("Goal" :in-theory (enable set-rsi))))

(defthm mv-nth-1-of-get-prefixes-of-set-rdi
  (equal (mv-nth 1 (get-prefixes proc-mode start-rip prefixes rex-byte cnt (set-rdi rdi x86)))
         (mv-nth 1 (get-prefixes proc-mode start-rip prefixes rex-byte cnt x86)))
  :hints (("Goal" :in-theory (enable set-rdi))))

(defthm mv-nth-1-of-get-prefixes-of-set-rsp
  (equal (mv-nth 1 (get-prefixes proc-mode start-rip prefixes rex-byte cnt (set-rsp rsp x86)))
         (mv-nth 1 (get-prefixes proc-mode start-rip prefixes rex-byte cnt x86)))
  :hints (("Goal" :in-theory (enable set-rsp))))

(defthm mv-nth-1-of-get-prefixes-of-set-rbp
  (equal (mv-nth 1 (get-prefixes proc-mode start-rip prefixes rex-byte cnt (set-rbp rbp x86)))
         (mv-nth 1 (get-prefixes proc-mode start-rip prefixes rex-byte cnt x86)))
  :hints (("Goal" :in-theory (enable set-rbp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm program-at-of-write
  (implies (and (separate :r (len bytes) prog-addr :r n addr) ; todo: gen the :rs
                (canonical-address-p prog-addr)
                (canonical-address-p (+ -1 (len bytes) prog-addr))
                (canonical-address-p addr)
                (implies (posp n)
                         (canonical-address-p (+ -1 n addr)))
                (app-view x86)
                (x86p x86))
           (equal (program-at prog-addr bytes (write n addr val x86))
                  (program-at prog-addr bytes x86)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (program-at)
                           (rb wb app-view)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; These can lead to nicer terms when rb-1 does not get fully converted to READ

(defthm mv-nth-1-of-rb-1-of-set-rip
  (equal (mv-nth 1 (rb-1 n addr r-x (set-rip rip x86)))
         (mv-nth 1 (rb-1 n addr r-x x86)))
  :hints (("Goal" :in-theory (enable rb-1 set-rip))))

(defthm mv-nth-1-of-rb-of-set-rip
  (equal (mv-nth 1 (rb n addr r-x (set-rip rip x86)))
         (mv-nth 1 (rb n addr r-x x86)))
  :hints (("Goal" :in-theory (enable rb set-rip))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; These can lead to nicer terms when rb does not get fully converted to READ

;; todo: more like this
(defthm mv-nth-1-of-rb-of-set-rax
  (equal (mv-nth 1 (rb n addr r-x (set-rax rax x86)))
         (mv-nth 1 (rb n addr r-x x86)))
  :hints (("Goal" :in-theory (enable rb set-rax))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm read-of-set-flag
  (equal (read n addr (set-flag flag val x86))
         (read n addr x86))
  :hints (("Goal" :in-theory (enable read memi))))

(defthm get-flag-of-write-byte
  (equal (get-flag flg (write-byte addr byte x86))
         (get-flag flg x86))
  :hints (("Goal" :in-theory (enable write-byte))))

(defthm get-flag-of-write
  (equal (get-flag flg (write n addr value x86))
         (get-flag flg x86))
  :hints (("Goal" :in-theory (enable write wb))))

(defthm get-flag-of-write-bytes
  (equal (get-flag flg (write-bytes addr values x86))
         (get-flag flg x86))
  :hints (("Goal" :in-theory (enable write-bytes))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm read-bytes-of-xw-irrel
  (implies (not (equal fld :mem))
           (equal (read-bytes addr x (xw fld index val x86))
                  (read-bytes addr x x86)))
  :hints (("Goal" :in-theory (enable read-bytes))))

;; todo: add more for more state changers!
(defthm read-bytes-of-set-flag
  (equal (read-bytes addr x (set-flag flag val x86))
         (read-bytes addr x x86))
  :hints (("Goal" :in-theory (enable read-bytes))))

(defthm read-bytes-of-set-undef
  (equal (read-bytes addr x (set-undef undef x86))
         (read-bytes addr x x86))
  :hints (("Goal" :in-theory (enable read-bytes))))

(defthm read-bytes-of-set-mxcsr
  (equal (read-bytes addr x (set-mxcsr mxcsr x86))
         (read-bytes addr x x86))
  :hints (("Goal" :in-theory (enable read-bytes))))

(defthm read-bytes-of-!rflags
  (equal (read-bytes addr x (!rflags rflags x86))
         (read-bytes addr x x86))
  :hints (("Goal" :in-theory (enable read-bytes))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
