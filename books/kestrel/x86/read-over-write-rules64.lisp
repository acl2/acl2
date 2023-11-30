; "Read over write" rules for our x86 state readers and writers
;
; Copyright (C) 2016-2023 Kestrel Technology, LLC
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
(include-book "support") ;todo: remove (factor out non-32-bit read-over-write stuff like mv-nth-0-of-get-prefixes-of-xw-of-irrel)

;; TODO: Make sure we have the complete set of these rules

;; The readers are: the 16 register readers, rip, get-flag, ctri, undef, read, (todo: read-byte?) (todo: rflags?), msri

;; The predicates are: x86p, alignment-checking-enabled-p, 64-bit-modep, app-view

;; The writers are: the 16 register writers, set-flag, set-undef, write, write-byte, !rflags (todo: why?)

(defthm undef-of-set-rip (equal (undef (set-rip rip x86)) (undef x86)) :hints (("Goal" :in-theory (enable undef))))

(defthm rip-of-set-undef (equal (rip (set-undef undef x86)) (rip x86)) :hints (("Goal" :in-theory (enable set-undef))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

(defthm undef-of-set-flag (equal (undef (set-flag flg val x86)) (undef x86)) :hints (("Goal" :in-theory (enable undef))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

(defthm undef-of-write-byte (equal (undef (write-byte base-addr byte x86)) (undef x86)) :hints (("Goal" :in-theory (enable write-byte))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

(defthm undef-of-write (equal (undef (write n base-addr val x86)) (undef x86)) :hints (("Goal" :in-theory (enable write))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
(defthm read-of-set-undef (equal (read n addr (set-undef val x86)) (read n addr x86)) :hints (("Goal" :in-theory (enable set-undef))))
(defthm read-of-!rflags (equal (read n addr (!rflags v x86)) (read n addr x86)) :hints (("Goal" :in-theory (enable read))))

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
(defthm x86p-of-set-undef (implies (x86p x86) (x86p (set-undef undef x86))) :hints (("Goal" :in-theory (enable set-undef))))
(defthm x86p-of-!rflags (implies (x86p x86) (x86p (!rflags v x86))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; (defthm rip-of-set-rax
;;   (equal (rip (set-rax rax x86))
;;          (rip x86))
;;   :hints (("Goal" :in-theory (enable set-rax))))

;; (defthm rip-of-set-rbx
;;   (equal (rip (set-rbx rbx x86))
;;          (rip x86))
;;   :hints (("Goal" :in-theory (enable set-rbx))))

;; (defthm rip-of-set-rcx
;;   (equal (rip (set-rcx rcx x86))
;;          (rip x86))
;;   :hints (("Goal" :in-theory (enable set-rcx))))

;; (defthm rip-of-set-rdx
;;   (equal (rip (set-rdx rdx x86))
;;          (rip x86))
;;   :hints (("Goal" :in-theory (enable set-rdx))))

;; (defthm rip-of-set-rsp
;;   (equal (rip (set-rsp rsp x86))
;;          (rip x86))
;;   :hints (("Goal" :in-theory (enable set-rsp))))

;; (defthm rip-of-set-rbp
;;   (equal (rip (set-rbp rbp x86))
;;          (rip x86))
;;   :hints (("Goal" :in-theory (enable set-rbp))))

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
(defthm alignment-checking-enabled-p-of-set-undef (equal (alignment-checking-enabled-p (set-undef undef x86)) (alignment-checking-enabled-p x86)) :hints (("Goal" :in-theory (enable set-undef))))

;improve?
(defthm alignment-checking-enabled-p-of-!rflags-of-xr
  (implies (equal (get-flag :ac x86_1) (get-flag :ac x86_2))
           (equal (alignment-checking-enabled-p (!rflags (xr ':rflags 'nil x86_1) x86_2))
                  (alignment-checking-enabled-p x86_2)))
  :hints (("Goal" :in-theory (enable !rflags alignment-checking-enabled-p get-flag))))

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
(defthm get-flag-of-set-undef (equal (get-flag flag (set-undef undef x86)) (get-flag flag x86)) :hints (("Goal" :in-theory (enable set-undef))))

(defthm get-flag-of-!rflags-of-xr
  (equal (get-flag flag (!rflags (xr ':rflags 'nil x86_1) x86_2))
         (get-flag flag x86_1))
  :hints (("Goal" :in-theory (enable !rflags get-flag))))

;; (defthm get-flag-of-write-byte-to-segment
;;   (equal (get-flag flag (write-byte-to-segment eff-addr seg-reg val x86))
;;          (get-flag flag x86))
;;   :hints (("Goal" :in-theory (enable write-byte-to-segment))))

;; (defthm get-flag-of-write-to-segment
;;   (equal (get-flag flag (write-to-segment n eff-addr seg-reg val x86))
;;          (get-flag flag x86))
;;   :hints (("Goal" :in-theory (enable write-to-segment))))

;; ;;;

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
(defthm 64-bit-modep-of-set-undef (equal (64-bit-modep (set-undef undef x86)) (64-bit-modep x86)) :hints (("Goal" :in-theory (enable set-undef))))
(defthm 64-bit-modep-of-!rflags (equal (64-bit-modep (!rflags v x86)) (64-bit-modep x86)))

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
(defthm app-view-of-set-undef (equal (app-view (set-undef undef x86)) (app-view x86)) :hints (("Goal" :in-theory (enable set-undef))))
(defthm app-view-of-!rflags (equal (app-view (!rflags v x86)) (app-view x86)))

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
;;                             acl2::bvplus-recollapse
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
;;                             acl2::bvplus-recollapse
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

(defthm ctri-of-set-rip (equal (x86isa::ctri i (set-rip rip x86)) (x86isa::ctri i x86)) :hints (("Goal" :in-theory (enable set-rip))))
(defthm ctri-of-set-rax (equal (x86isa::ctri i (set-rax val x86)) (x86isa::ctri i x86)) :hints (("Goal" :in-theory (enable set-rax))))
(defthm ctri-of-set-rbx (equal (x86isa::ctri i (set-rbx val x86)) (x86isa::ctri i x86)) :hints (("Goal" :in-theory (enable set-rbx))))
(defthm ctri-of-set-rcx (equal (x86isa::ctri i (set-rcx val x86)) (x86isa::ctri i x86)) :hints (("Goal" :in-theory (enable set-rcx))))
(defthm ctri-of-set-rdx (equal (x86isa::ctri i (set-rdx val x86)) (x86isa::ctri i x86)) :hints (("Goal" :in-theory (enable set-rdx))))
(defthm ctri-of-set-rsi (equal (x86isa::ctri i (set-rsi val x86)) (x86isa::ctri i x86)) :hints (("Goal" :in-theory (enable set-rsi))))
(defthm ctri-of-set-rdi (equal (x86isa::ctri i (set-rdi val x86)) (x86isa::ctri i x86)) :hints (("Goal" :in-theory (enable set-rdi))))
(defthm ctri-of-set-r8 (equal (x86isa::ctri i (set-r8 val x86)) (x86isa::ctri i x86)) :hints (("Goal" :in-theory (enable set-r8))))
(defthm ctri-of-set-r9 (equal (x86isa::ctri i (set-r9 val x86)) (x86isa::ctri i x86)) :hints (("Goal" :in-theory (enable set-r9))))
(defthm ctri-of-set-r10 (equal (x86isa::ctri i (set-r10 val x86)) (x86isa::ctri i x86)) :hints (("Goal" :in-theory (enable set-r10))))
(defthm ctri-of-set-r11 (equal (x86isa::ctri i (set-r11 val x86)) (x86isa::ctri i x86)) :hints (("Goal" :in-theory (enable set-r11))))
(defthm ctri-of-set-r12 (equal (x86isa::ctri i (set-r12 val x86)) (x86isa::ctri i x86)) :hints (("Goal" :in-theory (enable set-r12))))
(defthm ctri-of-set-r13 (equal (x86isa::ctri i (set-r13 val x86)) (x86isa::ctri i x86)) :hints (("Goal" :in-theory (enable set-r13))))
(defthm ctri-of-set-r14 (equal (x86isa::ctri i (set-r14 val x86)) (x86isa::ctri i x86)) :hints (("Goal" :in-theory (enable set-r14))))
(defthm ctri-of-set-r15 (equal (x86isa::ctri i (set-r15 val x86)) (x86isa::ctri i x86)) :hints (("Goal" :in-theory (enable set-r15))))
(defthm ctri-of-set-rsp (equal (x86isa::ctri i (set-rsp val x86)) (x86isa::ctri i x86)) :hints (("Goal" :in-theory (enable set-rsp))))
(defthm ctri-of-set-rbp (equal (x86isa::ctri i (set-rbp val x86)) (x86isa::ctri i x86)) :hints (("Goal" :in-theory (enable set-rbp))))
(defthm ctri-of-set-undef (equal (x86isa::ctri i (set-undef val x86)) (x86isa::ctri i x86)) :hints (("Goal" :in-theory (enable set-undef))))

(defthm ctri-of-xw-irrel
  (implies (not (equal :ctr fld))
           (equal (ctri i (xw fld index val x86))
                  (ctri i x86)))
  :hints (("Goal" :in-theory (enable ctri))))

(defthm ctri-of-write
  (equal (ctri i (write n base-addr val x86))
         (ctri i x86))
  :hints (("Goal" :in-theory (enable ctri))))

(defthm ctri-of-set-flag
  (equal (ctri i (set-flag flag val x86))
         (ctri i x86))
  :hints (("Goal" :in-theory (enable ctri))))

;todo: why is !rflags showing up?
(defthm ctri-of-!rflags
  (equal (ctri i (!rflags v x86))
         (ctri i x86)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm msri-of-set-rip (equal (x86isa::msri i (set-rip rip x86)) (x86isa::msri i x86)) :hints (("Goal" :in-theory (enable set-rip))))
(defthm msri-of-set-rax (equal (x86isa::msri i (set-rax val x86)) (x86isa::msri i x86)) :hints (("Goal" :in-theory (enable set-rax))))
(defthm msri-of-set-rbx (equal (x86isa::msri i (set-rbx val x86)) (x86isa::msri i x86)) :hints (("Goal" :in-theory (enable set-rbx))))
(defthm msri-of-set-rcx (equal (x86isa::msri i (set-rcx val x86)) (x86isa::msri i x86)) :hints (("Goal" :in-theory (enable set-rcx))))
(defthm msri-of-set-rdx (equal (x86isa::msri i (set-rdx val x86)) (x86isa::msri i x86)) :hints (("Goal" :in-theory (enable set-rdx))))
(defthm msri-of-set-rsi (equal (x86isa::msri i (set-rsi val x86)) (x86isa::msri i x86)) :hints (("Goal" :in-theory (enable set-rsi))))
(defthm msri-of-set-rdi (equal (x86isa::msri i (set-rdi val x86)) (x86isa::msri i x86)) :hints (("Goal" :in-theory (enable set-rdi))))
(defthm msri-of-set-r8 (equal (x86isa::msri i (set-r8 val x86)) (x86isa::msri i x86)) :hints (("Goal" :in-theory (enable set-r8))))
(defthm msri-of-set-r9 (equal (x86isa::msri i (set-r9 val x86)) (x86isa::msri i x86)) :hints (("Goal" :in-theory (enable set-r9))))
(defthm msri-of-set-r10 (equal (x86isa::msri i (set-r10 val x86)) (x86isa::msri i x86)) :hints (("Goal" :in-theory (enable set-r10))))
(defthm msri-of-set-r11 (equal (x86isa::msri i (set-r11 val x86)) (x86isa::msri i x86)) :hints (("Goal" :in-theory (enable set-r11))))
(defthm msri-of-set-r12 (equal (x86isa::msri i (set-r12 val x86)) (x86isa::msri i x86)) :hints (("Goal" :in-theory (enable set-r12))))
(defthm msri-of-set-r13 (equal (x86isa::msri i (set-r13 val x86)) (x86isa::msri i x86)) :hints (("Goal" :in-theory (enable set-r13))))
(defthm msri-of-set-r14 (equal (x86isa::msri i (set-r14 val x86)) (x86isa::msri i x86)) :hints (("Goal" :in-theory (enable set-r14))))
(defthm msri-of-set-r15 (equal (x86isa::msri i (set-r15 val x86)) (x86isa::msri i x86)) :hints (("Goal" :in-theory (enable set-r15))))
(defthm msri-of-set-rsp (equal (x86isa::msri i (set-rsp val x86)) (x86isa::msri i x86)) :hints (("Goal" :in-theory (enable set-rsp))))
(defthm msri-of-set-rbp (equal (x86isa::msri i (set-rbp val x86)) (x86isa::msri i x86)) :hints (("Goal" :in-theory (enable set-rbp))))
(defthm msri-of-set-undef (equal (x86isa::msri i (set-undef val x86)) (x86isa::msri i x86)) :hints (("Goal" :in-theory (enable set-undef))))

(defthm msri-of-write (equal (x86isa::msri i (write n base-addr val x86)) (x86isa::msri i x86)) :hints (("Goal" :in-theory (enable write))))
(defthm msri-of-set-flag (equal (x86isa::msri i (set-flag flg val x86)) (x86isa::msri i x86)) :hints (("Goal" :in-theory (enable rax))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm undef-of-!rflags (equal (undef (!rflags flags x86)) (undef x86)) :hints (("Goal" :in-theory (enable !rflags undef))))

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

;; todo: finish this:

(defthm mv-nth-0-of-rml-size-when-app-view
  (implies (and (not (equal :mem fld))
                (not (equal :app-view fld))
                (app-view x86) ; why?
                )
           (equal (mv-nth 0 (x86isa::rml-size nbytes addr r-x (xw fld index val x86)))
                  (mv-nth 0 (x86isa::rml-size nbytes addr r-x x86))))
  :hints (("Goal" :in-theory (enable x86isa::rml-size
                                     rb ;todo
                                     rb-1
                                     x86isa::rml128
                                     x86isa::rml48
                                     x86isa::rml80
                                     ))))

(encapsulate ()
  (local (in-theory (enable x86isa::rml80
                            x86isa::rml48
                            x86isa::rml128
                            x86isa::rme-size$inline)))

  (local (in-theory (disable ea-to-la$inline)))

  (defthm mv-nth-0-of-rme-size-of-set-rip (implies (app-view x86) (equal (mv-nth 0 (x86isa::rme-size p n e s r c (set-rip rip x86))) (mv-nth 0 (x86isa::rme-size p n e s r c x86)))) :hints (("Goal" :in-theory (enable set-rip))))
  (defthm mv-nth-0-of-rme-size-of-set-rax (implies (app-view x86) (equal (mv-nth 0 (x86isa::rme-size p n e s r c (set-rax val x86))) (mv-nth 0 (x86isa::rme-size p n e s r c x86)))) :hints (("Goal" :in-theory (enable set-rax))))
  (defthm mv-nth-0-of-rme-size-of-set-rbx (implies (app-view x86) (equal (mv-nth 0 (x86isa::rme-size p n e s r c (set-rbx val x86))) (mv-nth 0 (x86isa::rme-size p n e s r c x86)))) :hints (("Goal" :in-theory (enable set-rbx))))
  (defthm mv-nth-0-of-rme-size-of-set-rcx (implies (app-view x86) (equal (mv-nth 0 (x86isa::rme-size p n e s r c (set-rcx val x86))) (mv-nth 0 (x86isa::rme-size p n e s r c x86)))) :hints (("Goal" :in-theory (enable set-rcx))))
  (defthm mv-nth-0-of-rme-size-of-set-rdx (implies (app-view x86) (equal (mv-nth 0 (x86isa::rme-size p n e s r c (set-rdx val x86))) (mv-nth 0 (x86isa::rme-size p n e s r c x86)))) :hints (("Goal" :in-theory (enable set-rdx))))
  (defthm mv-nth-0-of-rme-size-of-set-rsi (implies (app-view x86) (equal (mv-nth 0 (x86isa::rme-size p n e s r c (set-rsi val x86))) (mv-nth 0 (x86isa::rme-size p n e s r c x86)))) :hints (("Goal" :in-theory (enable set-rsi))))
  (defthm mv-nth-0-of-rme-size-of-set-rdi (implies (app-view x86) (equal (mv-nth 0 (x86isa::rme-size p n e s r c (set-rdi val x86))) (mv-nth 0 (x86isa::rme-size p n e s r c x86)))) :hints (("Goal" :in-theory (enable set-rdi))))
  (defthm mv-nth-0-of-rme-size-of-set-r8 (implies (app-view x86) (equal (mv-nth 0 (x86isa::rme-size p n e s r c (set-r8 val x86))) (mv-nth 0 (x86isa::rme-size p n e s r c x86)))) :hints (("Goal" :in-theory (enable set-r8))))
  (defthm mv-nth-0-of-rme-size-of-set-r9 (implies (app-view x86) (equal (mv-nth 0 (x86isa::rme-size p n e s r c (set-r9 val x86))) (mv-nth 0 (x86isa::rme-size p n e s r c x86)))) :hints (("Goal" :in-theory (enable set-r9))))
  (defthm mv-nth-0-of-rme-size-of-set-r10 (implies (app-view x86) (equal (mv-nth 0 (x86isa::rme-size p n e s r c (set-r10 val x86))) (mv-nth 0 (x86isa::rme-size p n e s r c x86)))) :hints (("Goal" :in-theory (enable set-r10))))
  (defthm mv-nth-0-of-rme-size-of-set-r11 (implies (app-view x86) (equal (mv-nth 0 (x86isa::rme-size p n e s r c (set-r11 val x86))) (mv-nth 0 (x86isa::rme-size p n e s r c x86)))) :hints (("Goal" :in-theory (enable set-r11))))
  (defthm mv-nth-0-of-rme-size-of-set-r12 (implies (app-view x86) (equal (mv-nth 0 (x86isa::rme-size p n e s r c (set-r12 val x86))) (mv-nth 0 (x86isa::rme-size p n e s r c x86)))) :hints (("Goal" :in-theory (enable set-r12))))
  (defthm mv-nth-0-of-rme-size-of-set-r13 (implies (app-view x86) (equal (mv-nth 0 (x86isa::rme-size p n e s r c (set-r13 val x86))) (mv-nth 0 (x86isa::rme-size p n e s r c x86)))) :hints (("Goal" :in-theory (enable set-r13))))
  (defthm mv-nth-0-of-rme-size-of-set-r14 (implies (app-view x86) (equal (mv-nth 0 (x86isa::rme-size p n e s r c (set-r14 val x86))) (mv-nth 0 (x86isa::rme-size p n e s r c x86)))) :hints (("Goal" :in-theory (enable set-r14))))
  (defthm mv-nth-0-of-rme-size-of-set-r15 (implies (app-view x86) (equal (mv-nth 0 (x86isa::rme-size p n e s r c (set-r15 val x86))) (mv-nth 0 (x86isa::rme-size p n e s r c x86)))) :hints (("Goal" :in-theory (enable set-r15))))
  (defthm mv-nth-0-of-rme-size-of-set-rsp (implies (app-view x86) (equal (mv-nth 0 (x86isa::rme-size p n e s r c (set-rsp val x86))) (mv-nth 0 (x86isa::rme-size p n e s r c x86)))) :hints (("Goal" :in-theory (enable set-rsp))))
  (defthm mv-nth-0-of-rme-size-of-set-rbp (implies (app-view x86) (equal (mv-nth 0 (x86isa::rme-size p n e s r c (set-rbp val x86))) (mv-nth 0 (x86isa::rme-size p n e s r c x86)))) :hints (("Goal" :in-theory (enable set-rbp))))
  (defthm mv-nth-0-of-rme-size-of-set-undef (implies (app-view x86) (equal (mv-nth 0 (x86isa::rme-size p n e s r c (set-undef val x86))) (mv-nth 0 (x86isa::rme-size p n e s r c x86)))) :hints (("Goal" :in-theory (enable set-undef))))
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm segment-base-and-bounds-of-set-rip
  (equal (x86isa::segment-base-and-bounds proc-mode seg-reg (set-rip rip x86))
         (x86isa::segment-base-and-bounds proc-mode seg-reg x86))
  :hints (("Goal" :in-theory (enable set-rip))))

(defthm segment-base-and-bounds-of-set-rsp
  (equal (x86isa::segment-base-and-bounds proc-mode seg-reg (set-rsp rsp x86))
         (x86isa::segment-base-and-bounds proc-mode seg-reg x86))
  :hints (("Goal" :in-theory (enable set-rsp))))

(defthm segment-base-and-bounds-of-set-rbp
  (equal (x86isa::segment-base-and-bounds proc-mode seg-reg (set-rbp rbp x86))
         (x86isa::segment-base-and-bounds proc-mode seg-reg x86))
  :hints (("Goal" :in-theory (enable set-rbp))))

(defthm segment-base-and-bounds-of-set-rax
  (equal (x86isa::segment-base-and-bounds proc-mode seg-reg (set-rax rax x86))
         (x86isa::segment-base-and-bounds proc-mode seg-reg x86))
  :hints (("Goal" :in-theory (enable set-rax))))

(defthm segment-base-and-bounds-of-set-rdx
  (equal (x86isa::segment-base-and-bounds proc-mode seg-reg (set-rdx rdx x86))
         (x86isa::segment-base-and-bounds proc-mode seg-reg x86))
  :hints (("Goal" :in-theory (enable set-rdx))))

;todo: more!

(defthm segment-base-and-bounds-of-set-rsi
  (equal (x86isa::segment-base-and-bounds proc-mode seg-reg (set-rsi rsi x86))
         (x86isa::segment-base-and-bounds proc-mode seg-reg x86))
  :hints (("Goal" :in-theory (enable set-rsi))))

(defthm segment-base-and-bounds-of-set-rdi
  (equal (x86isa::segment-base-and-bounds proc-mode seg-reg (set-rdi rdi x86))
         (x86isa::segment-base-and-bounds proc-mode seg-reg x86))
  :hints (("Goal" :in-theory (enable set-rdi))))

;todo: not 64-bit-specific?
(defthm segment-base-and-bounds-of-set-flag
  (equal (x86isa::segment-base-and-bounds proc-mode seg-reg (set-flag flg val x86))
         (x86isa::segment-base-and-bounds proc-mode seg-reg x86))
  :hints (("Goal" :in-theory (enable set-flag))))

;slow!
(defthm segment-base-and-bounds-of-set-undef
  (equal (x86isa::segment-base-and-bounds proc-mode seg-reg (set-undef undef x86))
         (x86isa::segment-base-and-bounds proc-mode seg-reg x86))
  :hints (("Goal" :in-theory (enable set-undef))))

(defthm segment-base-and-bounds-of-write-byte
  (equal (x86isa::segment-base-and-bounds proc-mode seg-reg (write-byte base-addr byte x86))
         (x86isa::segment-base-and-bounds proc-mode seg-reg x86))
  :hints (("Goal" :in-theory (enable write-byte))))

(defthm segment-base-and-bounds-of-write
  (equal (x86isa::segment-base-and-bounds proc-mode seg-reg (write n base-addr val x86))
         (x86isa::segment-base-and-bounds proc-mode seg-reg x86))
  :hints (("Goal" :in-theory (enable write))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;todo: more like this!
(defthm mv-nth-0-of-get-prefixes-of-set-rip
  (equal (mv-nth 0 (x86isa::get-prefixes proc-mode start-rip prefixes rex-byte cnt (set-rip rip x86)))
         (mv-nth 0 (x86isa::get-prefixes proc-mode start-rip prefixes rex-byte cnt x86)))
  :hints (("Goal" :in-theory (enable set-rip))))

(defthm mv-nth-0-of-get-prefixes-of-set-rax
  (equal (mv-nth 0 (x86isa::get-prefixes proc-mode start-rip prefixes rex-byte cnt (set-rax rax x86)))
         (mv-nth 0 (x86isa::get-prefixes proc-mode start-rip prefixes rex-byte cnt x86)))
  :hints (("Goal" :in-theory (enable set-rax))))

(defthm mv-nth-0-of-get-prefixes-of-set-rdx
  (equal (mv-nth 0 (x86isa::get-prefixes proc-mode start-rip prefixes rex-byte cnt (set-rdx rdx x86)))
         (mv-nth 0 (x86isa::get-prefixes proc-mode start-rip prefixes rex-byte cnt x86)))
  :hints (("Goal" :in-theory (enable set-rdx))))

(defthm mv-nth-0-of-get-prefixes-of-set-rsi
  (equal (mv-nth 0 (x86isa::get-prefixes proc-mode start-rip prefixes rex-byte cnt (set-rsi rsi x86)))
         (mv-nth 0 (x86isa::get-prefixes proc-mode start-rip prefixes rex-byte cnt x86)))
  :hints (("Goal" :in-theory (enable set-rsi))))

(defthm mv-nth-0-of-get-prefixes-of-set-rdi
  (equal (mv-nth 0 (x86isa::get-prefixes proc-mode start-rip prefixes rex-byte cnt (set-rdi rdi x86)))
         (mv-nth 0 (x86isa::get-prefixes proc-mode start-rip prefixes rex-byte cnt x86)))
  :hints (("Goal" :in-theory (enable set-rdi))))

(defthm mv-nth-0-of-get-prefixes-of-set-rsp
  (equal (mv-nth 0 (x86isa::get-prefixes proc-mode start-rip prefixes rex-byte cnt (set-rsp rsp x86)))
         (mv-nth 0 (x86isa::get-prefixes proc-mode start-rip prefixes rex-byte cnt x86)))
  :hints (("Goal" :in-theory (enable set-rsp))))

(defthm mv-nth-0-of-get-prefixes-of-set-rbp
  (equal (mv-nth 0 (x86isa::get-prefixes proc-mode start-rip prefixes rex-byte cnt (set-rbp rbp x86)))
         (mv-nth 0 (x86isa::get-prefixes proc-mode start-rip prefixes rex-byte cnt x86)))
  :hints (("Goal" :in-theory (enable set-rbp))))

;;;

;todo: more like this!
(defthm mv-nth-1-of-get-prefixes-of-set-rip
  (equal (mv-nth 1 (x86isa::get-prefixes proc-mode start-rip prefixes rex-byte cnt (set-rip rip x86)))
         (mv-nth 1 (x86isa::get-prefixes proc-mode start-rip prefixes rex-byte cnt x86)))
  :hints (("Goal" :in-theory (enable set-rip))))

(defthm mv-nth-1-of-get-prefixes-of-set-rax
  (equal (mv-nth 1 (x86isa::get-prefixes proc-mode start-rip prefixes rex-byte cnt (set-rax rax x86)))
         (mv-nth 1 (x86isa::get-prefixes proc-mode start-rip prefixes rex-byte cnt x86)))
  :hints (("Goal" :in-theory (enable set-rax))))

(defthm mv-nth-1-of-get-prefixes-of-set-rdx
  (equal (mv-nth 1 (x86isa::get-prefixes proc-mode start-rip prefixes rex-byte cnt (set-rdx rdx x86)))
         (mv-nth 1 (x86isa::get-prefixes proc-mode start-rip prefixes rex-byte cnt x86)))
  :hints (("Goal" :in-theory (enable set-rdx))))

(defthm mv-nth-1-of-get-prefixes-of-set-rsi
  (equal (mv-nth 1 (x86isa::get-prefixes proc-mode start-rip prefixes rex-byte cnt (set-rsi rsi x86)))
         (mv-nth 1 (x86isa::get-prefixes proc-mode start-rip prefixes rex-byte cnt x86)))
  :hints (("Goal" :in-theory (enable set-rsi))))

(defthm mv-nth-1-of-get-prefixes-of-set-rdi
  (equal (mv-nth 1 (x86isa::get-prefixes proc-mode start-rip prefixes rex-byte cnt (set-rdi rdi x86)))
         (mv-nth 1 (x86isa::get-prefixes proc-mode start-rip prefixes rex-byte cnt x86)))
  :hints (("Goal" :in-theory (enable set-rdi))))

(defthm mv-nth-1-of-get-prefixes-of-set-rsp
  (equal (mv-nth 1 (x86isa::get-prefixes proc-mode start-rip prefixes rex-byte cnt (set-rsp rsp x86)))
         (mv-nth 1 (x86isa::get-prefixes proc-mode start-rip prefixes rex-byte cnt x86)))
  :hints (("Goal" :in-theory (enable set-rsp))))

(defthm mv-nth-1-of-get-prefixes-of-set-rbp
  (equal (mv-nth 1 (x86isa::get-prefixes proc-mode start-rip prefixes rex-byte cnt (set-rbp rbp x86)))
         (mv-nth 1 (x86isa::get-prefixes proc-mode start-rip prefixes rex-byte cnt x86)))
  :hints (("Goal" :in-theory (enable set-rbp))))
