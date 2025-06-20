; "Read over write" rules for our x86 state readers and writers
;
; Copyright (C) 2016-2019 Kestrel Technology, LLC
; Copyright (C) 2020-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

(include-book "support32") ; reduce?  but we need at least the memory readers
(include-book "register-readers-and-writers32")

(defthm esp-of-write-byte-to-segment
  (equal (esp (write-byte-to-segment eff-addr seg-reg val x86))
         (esp x86))
  :hints (("Goal" :in-theory (enable write-byte-to-segment))))

(defthm esp-of-write-to-segment
  (equal (esp (write-to-segment n eff-addr seg-reg val x86))
         (esp x86))
  :hints (("Goal" :in-theory (enable write-to-segment))))

;;;

(defthm read-byte-from-segment-of-set-reg-high
  (equal (read-byte-from-segment eff-addr seg-reg (set-reg-high reg val x86))
         (read-byte-from-segment eff-addr seg-reg x86))
  :hints (("Goal" :in-theory (enable set-reg-high))))

(defthm read-byte-from-segment-of-set-eip (equal (read-byte-from-segment eff-addr seg-reg (set-eip eip x86)) (read-byte-from-segment eff-addr seg-reg x86)) :hints (("Goal" :in-theory (enable set-eip))))
(defthm read-byte-from-segment-of-set-eax (equal (read-byte-from-segment eff-addr seg-reg (set-eax val x86)) (read-byte-from-segment eff-addr seg-reg x86)) :hints (("Goal" :in-theory (enable set-eax))))
(defthm read-byte-from-segment-of-set-ebx (equal (read-byte-from-segment eff-addr seg-reg (set-ebx val x86)) (read-byte-from-segment eff-addr seg-reg x86)) :hints (("Goal" :in-theory (enable set-ebx))))
(defthm read-byte-from-segment-of-set-ecx (equal (read-byte-from-segment eff-addr seg-reg (set-ecx val x86)) (read-byte-from-segment eff-addr seg-reg x86)) :hints (("Goal" :in-theory (enable set-ecx))))
(defthm read-byte-from-segment-of-set-edx (equal (read-byte-from-segment eff-addr seg-reg (set-edx val x86)) (read-byte-from-segment eff-addr seg-reg x86)) :hints (("Goal" :in-theory (enable set-edx))))
(defthm read-byte-from-segment-of-set-esp (equal (read-byte-from-segment eff-addr seg-reg (set-esp val x86)) (read-byte-from-segment eff-addr seg-reg x86)) :hints (("Goal" :in-theory (enable set-esp))))
(defthm read-byte-from-segment-of-set-ebp (equal (read-byte-from-segment eff-addr seg-reg (set-ebp val x86)) (read-byte-from-segment eff-addr seg-reg x86)) :hints (("Goal" :in-theory (enable set-ebp))))

(defthm read-byte-from-segment-of-set-mxcsr
  (equal (read-byte-from-segment eff-addr seg-reg (set-mxcsr mxcsr x86))
         (read-byte-from-segment eff-addr seg-reg x86))
  :hints (("Goal" :in-theory (enable set-mxcsr))))

;;;

(defthm read-from-segment-of-set-reg-high
  (equal (read-from-segment n eff-addr seg-reg (set-reg-high reg val x86))
         (read-from-segment n eff-addr seg-reg x86))
  :hints (("Goal" :in-theory (enable set-reg-high))))

(defthm read-from-segment-of-set-eip
  (equal (read-from-segment n eff-addr seg-reg (set-eip eip x86))
         (read-from-segment n eff-addr seg-reg x86))
  :hints (("Goal" :in-theory (enable set-eip))))

(defthm read-from-segment-of-set-eax
  (equal (read-from-segment n eff-addr seg-reg (set-eax val x86))
         (read-from-segment n eff-addr seg-reg x86))
  :hints (("Goal" :in-theory (enable set-eax))))

(defthm read-from-segment-of-set-ebx
  (equal (read-from-segment n eff-addr seg-reg (set-ebx val x86))
         (read-from-segment n eff-addr seg-reg x86))
  :hints (("Goal" :in-theory (enable set-ebx))))

(defthm read-from-segment-of-set-ecx
  (equal (read-from-segment n eff-addr seg-reg (set-ecx val x86))
         (read-from-segment n eff-addr seg-reg x86))
  :hints (("Goal" :in-theory (enable set-ecx))))

(defthm read-from-segment-of-set-edx
  (equal (read-from-segment n eff-addr seg-reg (set-edx val x86))
         (read-from-segment n eff-addr seg-reg x86))
  :hints (("Goal" :in-theory (enable set-edx))))

(defthm read-from-segment-of-set-esp
  (equal (read-from-segment n eff-addr seg-reg (set-esp val x86))
         (read-from-segment n eff-addr seg-reg x86))
  :hints (("Goal" :in-theory (enable set-esp))))

(defthm read-from-segment-of-set-ebp
  (equal (read-from-segment n eff-addr seg-reg (set-ebp val x86))
         (read-from-segment n eff-addr seg-reg x86))
  :hints (("Goal" :in-theory (enable set-ebp))))

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

;;;

(defthm segment-is-32-bitsp-of-set-reg-high
  (equal (segment-is-32-bitsp seg-reg (set-reg-high reg val x86))
         (segment-is-32-bitsp seg-reg x86))
  :hints (("Goal" :in-theory (enable set-reg-high))))

(defthm segment-is-32-bitsp-of-set-eax
  (equal (segment-is-32-bitsp seg-reg (set-eax eax x86))
         (segment-is-32-bitsp seg-reg x86))
  :hints (("Goal" :in-theory (enable set-eax))))

(defthm segment-is-32-bitsp-of-set-ebx
  (equal (segment-is-32-bitsp seg-reg (set-ebx ebx x86))
         (segment-is-32-bitsp seg-reg x86))
  :hints (("Goal" :in-theory (enable set-ebx))))

(defthm segment-is-32-bitsp-of-set-ecx
  (equal (segment-is-32-bitsp seg-reg (set-ecx ecx x86))
         (segment-is-32-bitsp seg-reg x86))
  :hints (("Goal" :in-theory (enable set-ecx))))

(defthm segment-is-32-bitsp-of-set-edx
  (equal (segment-is-32-bitsp seg-reg (set-edx edx x86))
         (segment-is-32-bitsp seg-reg x86))
  :hints (("Goal" :in-theory (enable set-edx))))

(defthm segment-is-32-bitsp-of-set-esp
  (equal (segment-is-32-bitsp seg-reg (set-esp esp x86))
         (segment-is-32-bitsp seg-reg x86))
  :hints (("Goal" :in-theory (enable set-esp))))

(defthm segment-is-32-bitsp-of-set-ebp
  (equal (segment-is-32-bitsp seg-reg (set-ebp ebp x86))
         (segment-is-32-bitsp seg-reg x86))
  :hints (("Goal" :in-theory (enable set-ebp))))

;;;

(defthm 32-bit-segment-size-of-set-reg-high
  (equal (32-bit-segment-size seg-reg (set-reg-high reg val x86))
         (32-bit-segment-size seg-reg x86))
  :hints (("Goal" :in-theory (enable set-reg-high))))

(defthm 32-bit-segment-size-of-set-eax
  (equal (32-bit-segment-size seg-reg (set-eax eax x86))
         (32-bit-segment-size seg-reg x86))
  :hints (("Goal" :in-theory (enable set-eax))))

(defthm 32-bit-segment-size-of-set-ebx
  (equal (32-bit-segment-size seg-reg (set-ebx ebx x86))
         (32-bit-segment-size seg-reg x86))
  :hints (("Goal" :in-theory (enable set-ebx))))

(defthm 32-bit-segment-size-of-set-ecx
  (equal (32-bit-segment-size seg-reg (set-ecx ecx x86))
         (32-bit-segment-size seg-reg x86))
  :hints (("Goal" :in-theory (enable set-ecx))))

(defthm 32-bit-segment-size-of-set-edx
  (equal (32-bit-segment-size seg-reg (set-edx edx x86))
         (32-bit-segment-size seg-reg x86))
  :hints (("Goal" :in-theory (enable set-edx))))

(defthm 32-bit-segment-size-of-set-esp
  (equal (32-bit-segment-size seg-reg (set-esp esp x86))
         (32-bit-segment-size seg-reg x86))
  :hints (("Goal" :in-theory (enable set-esp))))

(defthm 32-bit-segment-size-of-set-ebp
  (equal (32-bit-segment-size seg-reg (set-ebp ebp x86))
         (32-bit-segment-size seg-reg x86))
  :hints (("Goal" :in-theory (enable set-ebp))))

;open less in the proof?
(defthm 32-bit-segment-size-of-set-reg-high
  (equal (32-bit-segment-size seg-reg (set-reg-high reg val x86))
         (32-bit-segment-size seg-reg x86))
  :hints (("Goal" :in-theory (enable set-reg-high 32-bit-segment-size 32-bit-segment-start-and-size))))

;open less in the proof?
(defthm 32-bit-segment-size-of-set-eip
  (equal (32-bit-segment-size seg-reg (set-eip eip x86))
         (32-bit-segment-size seg-reg x86))
  :hints (("Goal" :in-theory (enable set-eip 32-bit-segment-size 32-bit-segment-start-and-size))))

;open less in the proof?
(defthm 32-bit-segment-size-of-write-byte-to-segment
  (equal (32-bit-segment-size seg-reg1 (write-byte-to-segment eff-addr seg-reg2 val x86))
         (32-bit-segment-size seg-reg1 x86))
  :hints (("Goal" :in-theory (enable write-byte-to-segment 32-bit-segment-size 32-bit-segment-start-and-size))))

(defthm 32-bit-segment-size-of-write-to-segment
  (equal (32-bit-segment-size seg-reg (write-to-segment n eff-addr seg-reg2 val x86))
         (32-bit-segment-size seg-reg x86))
  :hints (("Goal" :in-theory (enable 32-bit-segment-size))))

;;;

(defthm 32-bit-segment-start-of-set-reg-high
  (equal (32-bit-segment-start seg-reg (set-reg-high reg val x86))
         (32-bit-segment-start seg-reg x86))
  :hints (("Goal" :in-theory (enable set-reg-high))))

(defthm 32-bit-segment-start-of-set-eax
  (equal (32-bit-segment-start seg-reg (set-eax eax x86))
         (32-bit-segment-start seg-reg x86))
  :hints (("Goal" :in-theory (enable set-eax))))

(defthm 32-bit-segment-start-of-set-ebx
  (equal (32-bit-segment-start seg-reg (set-ebx ebx x86))
         (32-bit-segment-start seg-reg x86))
  :hints (("Goal" :in-theory (enable set-ebx))))

(defthm 32-bit-segment-start-of-set-ecx
  (equal (32-bit-segment-start seg-reg (set-ecx ecx x86))
         (32-bit-segment-start seg-reg x86))
  :hints (("Goal" :in-theory (enable set-ecx))))

(defthm 32-bit-segment-start-of-set-edx
  (equal (32-bit-segment-start seg-reg (set-edx edx x86))
         (32-bit-segment-start seg-reg x86))
  :hints (("Goal" :in-theory (enable set-edx))))

(defthm 32-bit-segment-start-of-set-esp
  (equal (32-bit-segment-start seg-reg (set-esp esp x86))
         (32-bit-segment-start seg-reg x86))
  :hints (("Goal" :in-theory (enable set-esp))))

(defthm 32-bit-segment-start-of-set-ebp
  (equal (32-bit-segment-start seg-reg (set-ebp ebp x86))
         (32-bit-segment-start seg-reg x86))
  :hints (("Goal" :in-theory (enable set-ebp))))

;;;

(defthm segment-expand-down-bit-of-set-reg-high
  (equal (segment-expand-down-bit seg-reg (set-reg-high reg val x86))
         (segment-expand-down-bit seg-reg x86))
  :hints (("Goal" :in-theory (enable set-reg-high))))

(defthm segment-expand-down-bit-of-set-eip
  (equal (segment-expand-down-bit seg-reg (set-eip eip x86))
         (segment-expand-down-bit seg-reg x86))
  :hints (("Goal" :in-theory (enable set-eip))))

(defthm segment-expand-down-bit-of-set-eax
  (equal (segment-expand-down-bit seg-reg (set-eax eax x86))
         (segment-expand-down-bit seg-reg x86))
  :hints (("Goal" :in-theory (enable set-eax))))

(defthm segment-expand-down-bit-of-set-ebx
  (equal (segment-expand-down-bit seg-reg (set-ebx ebx x86))
         (segment-expand-down-bit seg-reg x86))
  :hints (("Goal" :in-theory (enable set-ebx))))

(defthm segment-expand-down-bit-of-set-ecx
  (equal (segment-expand-down-bit seg-reg (set-ecx ecx x86))
         (segment-expand-down-bit seg-reg x86))
  :hints (("Goal" :in-theory (enable set-ecx))))

(defthm segment-expand-down-bit-of-set-edx
  (equal (segment-expand-down-bit seg-reg (set-edx edx x86))
         (segment-expand-down-bit seg-reg x86))
  :hints (("Goal" :in-theory (enable set-edx))))

(defthm segment-expand-down-bit-of-set-esp
  (equal (segment-expand-down-bit seg-reg (set-esp esp x86))
         (segment-expand-down-bit seg-reg x86))
  :hints (("Goal" :in-theory (enable set-esp))))

(defthm segment-expand-down-bit-of-set-ebp
  (equal (segment-expand-down-bit seg-reg (set-ebp ebp x86))
         (segment-expand-down-bit seg-reg x86))
  :hints (("Goal" :in-theory (enable set-ebp))))

(defthm segment-expand-down-bit-of-write-byte-to-segment
  (equal (segment-expand-down-bit seg-reg1 (write-byte-to-segment eff-addr seg-reg2 val x86))
         (segment-expand-down-bit seg-reg1 x86))
  :hints (("Goal" :in-theory (enable write-byte-to-segment 32-bit-segment-size 32-bit-segment-start-and-size))))

(defthm segment-expand-down-bit-of-write-to-segment
  (equal (segment-expand-down-bit seg-reg1 (write-to-segment n eff-addr seg-reg2 val x86))
         (segment-expand-down-bit seg-reg1 x86))
  :hints (("Goal" :in-theory (e/d (segment-expand-down-bit)
                                  (segment-expand-down-bit-intro)))))

;;;

(defthm well-formed-32-bit-segmentp-of-set-reg-high
  (equal (well-formed-32-bit-segmentp seg-reg (set-reg-high reg val x86))
         (well-formed-32-bit-segmentp seg-reg x86))
  :hints (("Goal" :in-theory (enable set-reg-high))))

(defthm well-formed-32-bit-segmentp-of-set-eax
  (equal (well-formed-32-bit-segmentp seg-reg (set-eax eax x86))
         (well-formed-32-bit-segmentp seg-reg x86))
  :hints (("Goal" :in-theory (enable set-eax))))

(defthm well-formed-32-bit-segmentp-of-set-ebx
  (equal (well-formed-32-bit-segmentp seg-reg (set-ebx ebx x86))
         (well-formed-32-bit-segmentp seg-reg x86))
  :hints (("Goal" :in-theory (enable set-ebx))))

(defthm well-formed-32-bit-segmentp-of-set-ecx
  (equal (well-formed-32-bit-segmentp seg-reg (set-ecx ecx x86))
         (well-formed-32-bit-segmentp seg-reg x86))
  :hints (("Goal" :in-theory (enable set-ecx))))

(defthm well-formed-32-bit-segmentp-of-set-edx
  (equal (well-formed-32-bit-segmentp seg-reg (set-edx edx x86))
         (well-formed-32-bit-segmentp seg-reg x86))
  :hints (("Goal" :in-theory (enable set-edx))))

(defthm well-formed-32-bit-segmentp-of-set-esp
  (equal (well-formed-32-bit-segmentp seg-reg (set-esp esp x86))
         (well-formed-32-bit-segmentp seg-reg x86))
  :hints (("Goal" :in-theory (enable set-esp))))

(defthm well-formed-32-bit-segmentp-of-set-ebp
  (equal (well-formed-32-bit-segmentp seg-reg (set-ebp ebp x86))
         (well-formed-32-bit-segmentp seg-reg x86))
  :hints (("Goal" :in-theory (enable set-ebp))))

(defthm well-formed-32-bit-segmentp-of-write-to-segment
  (equal (well-formed-32-bit-segmentp seg-reg1 (write-to-segment n eff-addr seg-reg2 val x86))
         (well-formed-32-bit-segmentp seg-reg1 x86))
  :hints (("Goal" :in-theory (enable write-to-segment))))

;;;

(defthm segments-separate-of-set-reg-high
  (equal (segments-separate seg-reg1 seg-reg2 (set-reg-high reg val x86))
         (segments-separate seg-reg1 seg-reg2 x86))
  :hints (("Goal" :in-theory (enable set-reg-high))))

(defthm segments-separate-of-set-eax
  (equal (segments-separate seg-reg1 seg-reg2 (set-eax eax x86))
         (segments-separate seg-reg1 seg-reg2 x86))
  :hints (("Goal" :in-theory (enable set-eax))))

(defthm segments-separate-of-set-ebx
  (equal (segments-separate seg-reg1 seg-reg2 (set-ebx ebx x86))
         (segments-separate seg-reg1 seg-reg2 x86))
  :hints (("Goal" :in-theory (enable set-ebx))))

(defthm segments-separate-of-set-ecx
  (equal (segments-separate seg-reg1 seg-reg2 (set-ecx ecx x86))
         (segments-separate seg-reg1 seg-reg2 x86))
  :hints (("Goal" :in-theory (enable set-ecx))))

(defthm segments-separate-of-set-edx
  (equal (segments-separate seg-reg1 seg-reg2 (set-edx edx x86))
         (segments-separate seg-reg1 seg-reg2 x86))
  :hints (("Goal" :in-theory (enable set-edx))))

(defthm segments-separate-of-set-esp
  (equal (segments-separate seg-reg1 seg-reg2 (set-esp esp x86))
         (segments-separate seg-reg1 seg-reg2 x86))
  :hints (("Goal" :in-theory (enable set-esp))))

(defthm segments-separate-of-set-ebp
  (equal (segments-separate seg-reg1 seg-reg2 (set-ebp ebp x86))
         (segments-separate seg-reg1 seg-reg2 x86))
  :hints (("Goal" :in-theory (enable set-ebp))))

;;;

(defthm code-and-stack-segments-separate-of-set-reg-high
  (equal (code-and-stack-segments-separate (set-reg-high reg val x86))
         (code-and-stack-segments-separate x86))
  :hints (("Goal" :in-theory (enable set-reg-high))))

(defthm code-and-stack-segments-separate-of-set-eax
  (equal (code-and-stack-segments-separate (set-eax eax x86))
         (code-and-stack-segments-separate x86))
  :hints (("Goal" :in-theory (enable set-eax))))

(defthm code-and-stack-segments-separate-of-set-ebx
  (equal (code-and-stack-segments-separate (set-ebx ebx x86))
         (code-and-stack-segments-separate x86))
  :hints (("Goal" :in-theory (enable set-ebx))))

(defthm code-and-stack-segments-separate-of-set-ecx
  (equal (code-and-stack-segments-separate (set-ecx ecx x86))
         (code-and-stack-segments-separate x86))
  :hints (("Goal" :in-theory (enable set-ecx))))

(defthm code-and-stack-segments-separate-of-set-edx
  (equal (code-and-stack-segments-separate (set-edx edx x86))
         (code-and-stack-segments-separate x86))
  :hints (("Goal" :in-theory (enable set-edx))))

(defthm code-and-stack-segments-separate-of-set-esp
  (equal (code-and-stack-segments-separate (set-esp esp x86))
         (code-and-stack-segments-separate x86))
  :hints (("Goal" :in-theory (enable set-esp))))

(defthm code-and-stack-segments-separate-of-set-ebp
  (equal (code-and-stack-segments-separate (set-ebp ebp x86))
         (code-and-stack-segments-separate x86))
  :hints (("Goal" :in-theory (enable set-ebp))))

;;;

(defthm alignment-checking-enabled-p-of-set-reg-high
  (equal (alignment-checking-enabled-p (set-reg-high reg val x86))
         (alignment-checking-enabled-p x86))
  :hints (("Goal" :in-theory (enable set-reg-high))))

(defthm alignment-checking-enabled-p-of-set-eax
  (equal (alignment-checking-enabled-p (set-eax eax x86))
         (alignment-checking-enabled-p x86))
  :hints (("Goal" :in-theory (enable set-eax))))

(defthm alignment-checking-enabled-p-of-set-ebx
  (equal (alignment-checking-enabled-p (set-ebx ebx x86))
         (alignment-checking-enabled-p x86))
  :hints (("Goal" :in-theory (enable set-ebx))))

(defthm alignment-checking-enabled-p-of-set-ecx
  (equal (alignment-checking-enabled-p (set-ecx ecx x86))
         (alignment-checking-enabled-p x86))
  :hints (("Goal" :in-theory (enable set-ecx))))

(defthm alignment-checking-enabled-p-of-set-edx
  (equal (alignment-checking-enabled-p (set-edx edx x86))
         (alignment-checking-enabled-p x86))
  :hints (("Goal" :in-theory (enable set-edx))))

(defthm alignment-checking-enabled-p-of-set-esp
  (equal (alignment-checking-enabled-p (set-esp esp x86))
         (alignment-checking-enabled-p x86))
  :hints (("Goal" :in-theory (enable set-esp))))

(defthm alignment-checking-enabled-p-of-set-ebp
  (equal (alignment-checking-enabled-p (set-ebp ebp x86))
         (alignment-checking-enabled-p x86))
  :hints (("Goal" :in-theory (enable set-ebp))))

;;;

(defthm get-flag-of-set-reg-high
  (equal (get-flag flag (set-reg-high reg val x86))
         (get-flag flag x86))
  :hints (("Goal" :in-theory (enable set-reg-high))))

(defthm get-flag-of-set-eip
  (equal (get-flag flag (set-eip eip x86))
         (get-flag flag x86))
  :hints (("Goal" :in-theory (enable set-eip))))

(defthm get-flag-of-set-eax
  (equal (get-flag flag (set-eax eax x86))
         (get-flag flag x86))
  :hints (("Goal" :in-theory (enable set-eax))))

(defthm get-flag-of-set-ebx
  (equal (get-flag flag (set-ebx ebx x86))
         (get-flag flag x86))
  :hints (("Goal" :in-theory (enable set-ebx))))

(defthm get-flag-of-set-ecx
  (equal (get-flag flag (set-ecx ecx x86))
         (get-flag flag x86))
  :hints (("Goal" :in-theory (enable set-ecx))))

(defthm get-flag-of-set-edx
  (equal (get-flag flag (set-edx edx x86))
         (get-flag flag x86))
  :hints (("Goal" :in-theory (enable set-edx))))

(defthm get-flag-of-set-esp
  (equal (get-flag flag (set-esp esp x86))
         (get-flag flag x86))
  :hints (("Goal" :in-theory (enable set-esp))))

(defthm get-flag-of-set-ebp
  (equal (get-flag flag (set-ebp ebp x86))
         (get-flag flag x86))
  :hints (("Goal" :in-theory (enable set-ebp))))

(defthm get-flag-of-write-byte-to-segment
  (equal (get-flag flag (write-byte-to-segment eff-addr seg-reg val x86))
         (get-flag flag x86))
  :hints (("Goal" :in-theory (enable write-byte-to-segment))))

(defthm get-flag-of-write-to-segment
  (equal (get-flag flag (write-to-segment n eff-addr seg-reg val x86))
         (get-flag flag x86))
  :hints (("Goal" :in-theory (enable write-to-segment))))

;;;

(defthm eff-addr-okp-of-set-reg-high
  (equal (eff-addr-okp eff-addr seg-reg (set-reg-high reg val x86))
         (eff-addr-okp eff-addr seg-reg x86))
  :hints (("Goal" :in-theory (enable set-reg-high))))

(defthm eff-addr-okp-of-set-eax
  (equal (eff-addr-okp eff-addr seg-reg (set-eax eax x86))
         (eff-addr-okp eff-addr seg-reg x86))
  :hints (("Goal" :in-theory (enable set-eax))))

(defthm eff-addr-okp-of-set-ebx
  (equal (eff-addr-okp eff-addr seg-reg (set-ebx ebx x86))
         (eff-addr-okp eff-addr seg-reg x86))
  :hints (("Goal" :in-theory (enable set-ebx))))

(defthm eff-addr-okp-of-set-ecx
  (equal (eff-addr-okp eff-addr seg-reg (set-ecx ecx x86))
         (eff-addr-okp eff-addr seg-reg x86))
  :hints (("Goal" :in-theory (enable set-ecx))))

(defthm eff-addr-okp-of-set-edx
  (equal (eff-addr-okp eff-addr seg-reg (set-edx edx x86))
         (eff-addr-okp eff-addr seg-reg x86))
  :hints (("Goal" :in-theory (enable set-edx))))

(defthm eff-addr-okp-of-set-esp
  (equal (eff-addr-okp eff-addr seg-reg (set-esp esp x86))
         (eff-addr-okp eff-addr seg-reg x86))
  :hints (("Goal" :in-theory (enable set-esp))))

(defthm eff-addr-okp-of-set-ebp
  (equal (eff-addr-okp eff-addr seg-reg (set-ebp ebp x86))
         (eff-addr-okp eff-addr seg-reg x86))
  :hints (("Goal" :in-theory (enable set-ebp))))

;;;

(defthm eff-addrs-okp-of-set-reg-high
  (equal (eff-addrs-okp n eff-addr seg-reg (set-reg-high reg high x86))
         (eff-addrs-okp n eff-addr seg-reg x86))
  :hints (("Goal" :in-theory (enable set-reg-high))))

(defthm eff-addrs-okp-of-set-eax
  (equal (eff-addrs-okp n eff-addr seg-reg (set-eax eax x86))
         (eff-addrs-okp n eff-addr seg-reg x86))
  :hints (("Goal" :in-theory (enable set-eax))))

(defthm eff-addrs-okp-of-set-ebx
  (equal (eff-addrs-okp n eff-addr seg-reg (set-ebx ebx x86))
         (eff-addrs-okp n eff-addr seg-reg x86))
  :hints (("Goal" :in-theory (enable set-ebx))))

(defthm eff-addrs-okp-of-set-ecx
  (equal (eff-addrs-okp n eff-addr seg-reg (set-ecx ecx x86))
         (eff-addrs-okp n eff-addr seg-reg x86))
  :hints (("Goal" :in-theory (enable set-ecx))))

(defthm eff-addrs-okp-of-set-edx
  (equal (eff-addrs-okp n eff-addr seg-reg (set-edx edx x86))
         (eff-addrs-okp n eff-addr seg-reg x86))
  :hints (("Goal" :in-theory (enable set-edx))))

(defthm eff-addrs-okp-of-set-esp
  (equal (eff-addrs-okp n eff-addr seg-reg (set-esp esp x86))
         (eff-addrs-okp n eff-addr seg-reg x86))
  :hints (("Goal" :in-theory (enable set-esp))))

(defthm eff-addrs-okp-of-set-ebp
  (equal (eff-addrs-okp n eff-addr seg-reg (set-ebp ebp x86))
         (eff-addrs-okp n eff-addr seg-reg x86))
  :hints (("Goal" :in-theory (enable set-ebp))))

;;;

(defthm 64-bit-modep-of-set-reg-high
  (equal (64-bit-modep (set-reg-high reg val x86))
         (64-bit-modep x86))
  :hints (("Goal" :in-theory (enable set-reg-high))))

(defthm 64-bit-modep-of-set-eip
  (equal (64-bit-modep (set-eip eip x86))
         (64-bit-modep x86))
  :hints (("Goal" :in-theory (enable set-eip))))

(defthm 64-bit-modep-of-set-eax
  (equal (64-bit-modep (set-eax eax x86))
         (64-bit-modep x86))
  :hints (("Goal" :in-theory (enable set-eax))))

(defthm 64-bit-modep-of-set-ebx
  (equal (64-bit-modep (set-ebx ebx x86))
         (64-bit-modep x86))
  :hints (("Goal" :in-theory (enable set-ebx))))

(defthm 64-bit-modep-of-set-ecx
  (equal (64-bit-modep (set-ecx ecx x86))
         (64-bit-modep x86))
  :hints (("Goal" :in-theory (enable set-ecx))))

(defthm 64-bit-modep-of-set-edx
  (equal (64-bit-modep (set-edx edx x86))
         (64-bit-modep x86))
  :hints (("Goal" :in-theory (enable set-edx))))

(defthm 64-bit-modep-of-set-esp
  (equal (64-bit-modep (set-esp esp x86))
         (64-bit-modep x86))
  :hints (("Goal" :in-theory (enable set-esp))))

(defthm 64-bit-modep-of-set-ebp
  (equal (64-bit-modep (set-ebp ebp x86))
         (64-bit-modep x86))
  :hints (("Goal" :in-theory (enable set-ebp))))

;;;

(defthm app-view-of-set-reg-high
  (equal (app-view (set-reg-high reg val x86))
         (app-view x86))
  :hints (("Goal" :in-theory (enable set-reg-high))))

(defthm app-view-of-set-eip
  (equal (app-view (set-eip eip x86))
         (app-view x86))
  :hints (("Goal" :in-theory (enable set-eip))))

(defthm app-view-of-set-eax
  (equal (app-view (set-eax eax x86))
         (app-view x86))
  :hints (("Goal" :in-theory (enable set-eax))))

(defthm app-view-of-set-ebx
  (equal (app-view (set-ebx ebx x86))
         (app-view x86))
  :hints (("Goal" :in-theory (enable set-ebx))))

(defthm app-view-of-set-ecx
  (equal (app-view (set-ecx ecx x86))
         (app-view x86))
  :hints (("Goal" :in-theory (enable set-ecx))))

(defthm app-view-of-set-edx
  (equal (app-view (set-edx edx x86))
         (app-view x86))
  :hints (("Goal" :in-theory (enable set-edx))))

(defthm app-view-of-set-esp
  (equal (app-view (set-esp esp x86))
         (app-view x86))
  :hints (("Goal" :in-theory (enable set-esp))))

(defthm app-view-of-set-ebp
  (equal (app-view (set-ebp ebp x86))
         (app-view x86))
  :hints (("Goal" :in-theory (enable set-ebp))))

(defthm app-view-of-write-to-segment
  (equal (app-view (write-to-segment n eff-addr seg-reg val x86))
         (app-view x86)))

;;;

(defthm code-segment-assumptions32-for-code-of-set-reg-high
  (equal (code-segment-assumptions32-for-code code offset (set-reg-high reg val x86))
         (code-segment-assumptions32-for-code code offset x86))
  :hints (("Goal" :in-theory (enable set-reg-high))))

(defthm code-segment-assumptions32-for-code-of-set-eax
  (equal (code-segment-assumptions32-for-code code offset (set-eax eax x86))
         (code-segment-assumptions32-for-code code offset x86))
  :hints (("Goal" :in-theory (enable set-eax))))

(defthm code-segment-assumptions32-for-code-of-set-ebx
  (equal (code-segment-assumptions32-for-code code offset (set-ebx ebx x86))
         (code-segment-assumptions32-for-code code offset x86))
  :hints (("Goal" :in-theory (enable set-ebx))))

(defthm code-segment-assumptions32-for-code-of-set-ecx
  (equal (code-segment-assumptions32-for-code code offset (set-ecx ecx x86))
         (code-segment-assumptions32-for-code code offset x86))
  :hints (("Goal" :in-theory (enable set-ecx))))

(defthm code-segment-assumptions32-for-code-of-set-edx
  (equal (code-segment-assumptions32-for-code code offset (set-edx edx x86))
         (code-segment-assumptions32-for-code code offset x86))
  :hints (("Goal" :in-theory (enable set-edx))))

(defthm code-segment-assumptions32-for-code-of-set-esp
  (equal (code-segment-assumptions32-for-code code offset (set-esp esp x86))
         (code-segment-assumptions32-for-code code offset x86))
  :hints (("Goal" :in-theory (enable set-esp))))

(defthm code-segment-assumptions32-for-code-of-set-ebp
  (equal (code-segment-assumptions32-for-code code offset (set-ebp ebp x86))
         (code-segment-assumptions32-for-code code offset x86))
  :hints (("Goal" :in-theory (enable set-ebp))))

;;;

(defthm segment-base-and-bounds-of-set-reg-high
  (equal (segment-base-and-bounds proc-mode seg-reg (set-reg-high reg val x86))
         (segment-base-and-bounds proc-mode seg-reg x86))
  :hints (("Goal" :in-theory (enable set-reg-high))))

(defthm segment-base-and-bounds-of-set-eax
  (equal (segment-base-and-bounds proc-mode seg-reg (set-eax eax x86))
         (segment-base-and-bounds proc-mode seg-reg x86))
  :hints (("Goal" :in-theory (enable set-eax))))

(defthm segment-base-and-bounds-of-set-ebx
  (equal (segment-base-and-bounds proc-mode seg-reg (set-ebx ebx x86))
         (segment-base-and-bounds proc-mode seg-reg x86))
  :hints (("Goal" :in-theory (enable set-ebx))))

(defthm segment-base-and-bounds-of-set-ecx
  (equal (segment-base-and-bounds proc-mode seg-reg (set-ecx ecx x86))
         (segment-base-and-bounds proc-mode seg-reg x86))
  :hints (("Goal" :in-theory (enable set-ecx))))

(defthm segment-base-and-bounds-of-set-edx
  (equal (segment-base-and-bounds proc-mode seg-reg (set-edx edx x86))
         (segment-base-and-bounds proc-mode seg-reg x86))
  :hints (("Goal" :in-theory (enable set-edx))))

(defthm segment-base-and-bounds-of-set-esp
  (equal (segment-base-and-bounds proc-mode seg-reg (set-esp esp x86))
         (segment-base-and-bounds proc-mode seg-reg x86))
  :hints (("Goal" :in-theory (enable set-esp))))

(defthm segment-base-and-bounds-of-set-ebp
  (equal (segment-base-and-bounds proc-mode seg-reg (set-ebp ebp x86))
         (segment-base-and-bounds proc-mode seg-reg x86))
  :hints (("Goal" :in-theory (enable set-ebp))))

;;;

(defthm data-segment-writeable-bit-of-set-reg-high
  (equal (data-segment-writeable-bit seg-reg (set-reg-high reg val x86))
         (data-segment-writeable-bit seg-reg x86))
  :hints (("Goal" :in-theory (enable set-reg-high))))

(defthm data-segment-writeable-bit-of-set-eip
  (equal (data-segment-writeable-bit seg-reg (set-eip eip x86))
         (data-segment-writeable-bit seg-reg x86))
  :hints (("Goal" :in-theory (enable set-eip))))

(defthm data-segment-writeable-bit-of-set-eax
  (equal (data-segment-writeable-bit seg-reg (set-eax eax x86))
         (data-segment-writeable-bit seg-reg x86))
  :hints (("Goal" :in-theory (enable set-eax))))

(defthm data-segment-writeable-bit-of-set-ebx
  (equal (data-segment-writeable-bit seg-reg (set-ebx ebx x86))
         (data-segment-writeable-bit seg-reg x86))
  :hints (("Goal" :in-theory (enable set-ebx))))

(defthm data-segment-writeable-bit-of-set-ecx
  (equal (data-segment-writeable-bit seg-reg (set-ecx ecx x86))
         (data-segment-writeable-bit seg-reg x86))
  :hints (("Goal" :in-theory (enable set-ecx))))

(defthm data-segment-writeable-bit-of-set-edx
  (equal (data-segment-writeable-bit seg-reg (set-edx edx x86))
         (data-segment-writeable-bit seg-reg x86))
  :hints (("Goal" :in-theory (enable set-edx))))

(defthm data-segment-writeable-bit-of-set-esp
  (equal (data-segment-writeable-bit seg-reg (set-esp esp x86))
         (data-segment-writeable-bit seg-reg x86))
  :hints (("Goal" :in-theory (enable set-esp))))

(defthm data-segment-writeable-bit-of-set-ebp
  (equal (data-segment-writeable-bit seg-reg (set-ebp ebp x86))
         (data-segment-writeable-bit seg-reg x86))
  :hints (("Goal" :in-theory (enable set-ebp))))

(defthm data-segment-writeable-bit-of-write-byte-to-segment
  (equal (data-segment-writeable-bit seg-reg1 (write-byte-to-segment eff-addr seg-reg2 val x86))
         (data-segment-writeable-bit seg-reg1 x86))
  :hints (("Goal" :in-theory (enable write-byte-to-segment))))

(defthm data-segment-writeable-bit-of-write-to-segment
  (equal (data-segment-writeable-bit seg-reg1 (write-to-segment n eff-addr seg-reg2 val x86))
         (data-segment-writeable-bit seg-reg1 x86))
  :hints (("Goal" :in-theory (enable write-to-segment))))

;;;

(defthm code-segment-readable-bit-of-set-reg-high
  (equal (code-segment-readable-bit (set-reg-high reg val x86))
         (code-segment-readable-bit x86))
  :hints (("Goal" :in-theory (enable set-reg-high))))

(defthm code-segment-readable-bit-of-set-eip
  (equal (code-segment-readable-bit (set-eip eip x86))
         (code-segment-readable-bit x86))
  :hints (("Goal" :in-theory (enable set-eip))))

(defthm code-segment-readable-bit-of-set-eax
  (equal (code-segment-readable-bit (set-eax eax x86))
         (code-segment-readable-bit x86))
  :hints (("Goal" :in-theory (enable set-eax))))

(defthm code-segment-readable-bit-of-set-ebx
  (equal (code-segment-readable-bit (set-ebx ebx x86))
         (code-segment-readable-bit x86))
  :hints (("Goal" :in-theory (enable set-ebx))))

(defthm code-segment-readable-bit-of-set-ecx
  (equal (code-segment-readable-bit (set-ecx ecx x86))
         (code-segment-readable-bit x86))
  :hints (("Goal" :in-theory (enable set-ecx))))

(defthm code-segment-readable-bit-of-set-edx
  (equal (code-segment-readable-bit (set-edx edx x86))
         (code-segment-readable-bit x86))
  :hints (("Goal" :in-theory (enable set-edx))))

(defthm code-segment-readable-bit-of-set-esp
  (equal (code-segment-readable-bit (set-esp esp x86))
         (code-segment-readable-bit x86))
  :hints (("Goal" :in-theory (enable set-esp))))

(defthm code-segment-readable-bit-of-set-ebp
  (equal (code-segment-readable-bit (set-ebp ebp x86))
         (code-segment-readable-bit x86))
  :hints (("Goal" :in-theory (enable set-ebp))))

(defthm code-segment-readable-bit-of-write-byte-to-segment
  (equal (code-segment-readable-bit (write-byte-to-segment eff-addr seg-reg2 val x86))
         (code-segment-readable-bit x86))
  :hints (("Goal" :in-theory (enable write-byte-to-segment))))

(defthm code-segment-readable-bit-of-write-to-segment
  (equal (code-segment-readable-bit (write-to-segment n eff-addr seg-reg2 val x86))
         (code-segment-readable-bit x86))
  :hints (("Goal" :in-theory (enable write-to-segment))))

;;;

(defthm code-segment-well-formedp-of-set-reg-high
  (equal (code-segment-well-formedp (set-reg-high reg val x86))
         (code-segment-well-formedp x86))
  :hints (("Goal" :in-theory (enable set-reg-high))))

(defthm code-segment-well-formedp-of-set-eax
  (equal (code-segment-well-formedp (set-eax eax x86))
         (code-segment-well-formedp x86))
  :hints (("Goal" :in-theory (enable set-eax))))

(defthm code-segment-well-formedp-of-set-ebx
  (equal (code-segment-well-formedp (set-ebx ebx x86))
         (code-segment-well-formedp x86))
  :hints (("Goal" :in-theory (enable set-ebx))))

(defthm code-segment-well-formedp-of-set-ecx
  (equal (code-segment-well-formedp (set-ecx ecx x86))
         (code-segment-well-formedp x86))
  :hints (("Goal" :in-theory (enable set-ecx))))

(defthm code-segment-well-formedp-of-set-edx
  (equal (code-segment-well-formedp (set-edx edx x86))
         (code-segment-well-formedp x86))
  :hints (("Goal" :in-theory (enable set-edx))))

(defthm code-segment-well-formedp-of-set-esp
  (equal (code-segment-well-formedp (set-esp esp x86))
         (code-segment-well-formedp x86))
  :hints (("Goal" :in-theory (enable set-esp))))

(defthm code-segment-well-formedp-of-set-ebp
  (equal (code-segment-well-formedp (set-ebp ebp x86))
         (code-segment-well-formedp x86))
  :hints (("Goal" :in-theory (enable set-ebp))))

(defthm code-segment-well-formedp-of-write-to-segment
  (equal (code-segment-well-formedp (write-to-segment n eff-addr seg-reg val x86))
         (code-segment-well-formedp x86))
  :hints (("Goal" :in-theory (enable code-segment-well-formedp
                                     code-and-stack-segments-separate
                                     32-bit-segment-size))))

;;;

(defthm stack-segment-assumptions32-of-write-to-segment
  (equal (stack-segment-assumptions32 stack-slots-needed (write-to-segment n eff-addr seg-reg val x86))
         (stack-segment-assumptions32 stack-slots-needed x86))
  :hints (("Goal" :in-theory (e/d () (;; x86isa::rgfi-is-i64p
                                      ;; x86isa::seg-hidden-basei-is-n64p
                                      ;; x86isa::seg-hidden-limiti-is-n32p
                                      ;; x86isa::seg-hidden-attri-is-n16p
                                      ))))) ;bad forcing

;;;

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

;;;

(defthm read-stack-dword-of-set-reg-high
  (equal (read-stack-dword eff-addr (set-reg-high reg val x86))
         (read-stack-dword eff-addr x86))
  :hints (("Goal" :in-theory (enable set-reg-high))))

(defthm read-stack-dword-of-set-eip
  (equal (read-stack-dword eff-addr (set-eip val x86))
         (read-stack-dword eff-addr x86))
  :hints (("Goal" :in-theory (enable set-eip))))

(defthm read-stack-dword-of-set-eax
  (equal (read-stack-dword eff-addr (set-eax val x86))
         (read-stack-dword eff-addr x86))
  :hints (("Goal" :in-theory (enable set-eax))))

(defthm read-stack-dword-of-set-ebx
  (equal (read-stack-dword eff-addr (set-ebx val x86))
         (read-stack-dword eff-addr x86))
  :hints (("Goal" :in-theory (enable set-ebx))))

(defthm read-stack-dword-of-set-ecx
  (equal (read-stack-dword eff-addr (set-ecx val x86))
         (read-stack-dword eff-addr x86))
  :hints (("Goal" :in-theory (enable set-ecx))))

(defthm read-stack-dword-of-set-edx
  (equal (read-stack-dword eff-addr (set-edx val x86))
         (read-stack-dword eff-addr x86))
  :hints (("Goal" :in-theory (enable set-edx))))

(defthm read-stack-dword-of-set-esp
  (equal (read-stack-dword eff-addr (set-esp val x86))
         (read-stack-dword eff-addr x86))
  :hints (("Goal" :in-theory (enable set-esp))))

(defthm read-stack-dword-of-set-ebp
  (equal (read-stack-dword eff-addr (set-ebp val x86))
         (read-stack-dword eff-addr x86))
  :hints (("Goal" :in-theory (enable set-ebp))))

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

(defthm undef-of-set-reg-high (equal (undef (set-reg-high reg val x86)) (undef x86)) :hints (("Goal" :in-theory (enable undef set-reg-high))))
(defthm undef-of-set-eip (equal (undef (set-eip val x86)) (undef x86)) :hints (("Goal" :in-theory (enable undef set-eip))))
(defthm undef-of-set-eax (equal (undef (set-eax val x86)) (undef x86)) :hints (("Goal" :in-theory (enable undef set-eax))))
(defthm undef-of-set-ebx (equal (undef (set-ebx val x86)) (undef x86)) :hints (("Goal" :in-theory (enable undef set-ebx))))
(defthm undef-of-set-ecx (equal (undef (set-ecx val x86)) (undef x86)) :hints (("Goal" :in-theory (enable undef set-ecx))))
(defthm undef-of-set-edx (equal (undef (set-edx val x86)) (undef x86)) :hints (("Goal" :in-theory (enable undef set-edx))))
;; (defthm undef-of-set-esi (equal (undef (set-esi val x86)) (undef x86)) :hints (("Goal" :in-theory (enable undef set-esi))))
;; (defthm undef-of-set-edi (equal (undef (set-edi val x86)) (undef x86)) :hints (("Goal" :in-theory (enable undef set-edi))))
(defthm undef-of-set-esp (equal (undef (set-esp val x86)) (undef x86)) :hints (("Goal" :in-theory (enable undef set-esp))))
(defthm undef-of-set-ebp (equal (undef (set-ebp val x86)) (undef x86)) :hints (("Goal" :in-theory (enable undef set-ebp))))

(defthm mxcsr-of-set-reg-high (equal (mxcsr (set-reg-high reg val x86)) (mxcsr x86)) :hints (("Goal" :in-theory (enable mxcsr set-reg-high))))
(defthm mxcsr-of-set-eip (equal (mxcsr (set-eip val x86)) (mxcsr x86)) :hints (("Goal" :in-theory (enable mxcsr set-eip))))
(defthm mxcsr-of-set-eax (equal (mxcsr (set-eax val x86)) (mxcsr x86)) :hints (("Goal" :in-theory (enable mxcsr set-eax))))
(defthm mxcsr-of-set-ebx (equal (mxcsr (set-ebx val x86)) (mxcsr x86)) :hints (("Goal" :in-theory (enable mxcsr set-ebx))))
(defthm mxcsr-of-set-ecx (equal (mxcsr (set-ecx val x86)) (mxcsr x86)) :hints (("Goal" :in-theory (enable mxcsr set-ecx))))
(defthm mxcsr-of-set-edx (equal (mxcsr (set-edx val x86)) (mxcsr x86)) :hints (("Goal" :in-theory (enable mxcsr set-edx))))
;; (defthm mxcsr-of-set-esi (equal (mxcsr (set-esi val x86)) (mxcsr x86)) :hints (("Goal" :in-theory (enable mxcsr set-esi))))
;; (defthm mxcsr-of-set-edi (equal (mxcsr (set-edi val x86)) (mxcsr x86)) :hints (("Goal" :in-theory (enable mxcsr set-edi))))
(defthm mxcsr-of-set-esp (equal (mxcsr (set-esp val x86)) (mxcsr x86)) :hints (("Goal" :in-theory (enable mxcsr set-esp))))
(defthm mxcsr-of-set-ebp (equal (mxcsr (set-ebp val x86)) (mxcsr x86)) :hints (("Goal" :in-theory (enable mxcsr set-ebp))))

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

(defthm ms-of-set-reg-high (equal (ms (set-reg-high reg val x86)) (ms x86)) :hints (("Goal" :in-theory (enable ms set-reg-high))))
(defthm ms-of-set-eip (equal (ms (set-eip val x86)) (ms x86)) :hints (("Goal" :in-theory (enable ms set-eip))))
(defthm ms-of-set-eax (equal (ms (set-eax val x86)) (ms x86)) :hints (("Goal" :in-theory (enable ms set-eax))))
(defthm ms-of-set-ebx (equal (ms (set-ebx val x86)) (ms x86)) :hints (("Goal" :in-theory (enable ms set-ebx))))
(defthm ms-of-set-ecx (equal (ms (set-ecx val x86)) (ms x86)) :hints (("Goal" :in-theory (enable ms set-ecx))))
(defthm ms-of-set-edx (equal (ms (set-edx val x86)) (ms x86)) :hints (("Goal" :in-theory (enable ms set-edx))))
;; (defthm ms-of-set-esi (equal (ms (set-esi val x86)) (ms x86)) :hints (("Goal" :in-theory (enable ms set-esi))))
;; (defthm ms-of-set-edi (equal (ms (set-edi val x86)) (ms x86)) :hints (("Goal" :in-theory (enable ms set-edi))))
(defthm ms-of-set-esp (equal (ms (set-esp val x86)) (ms x86)) :hints (("Goal" :in-theory (enable ms set-esp))))
(defthm ms-of-set-ebp (equal (ms (set-ebp val x86)) (ms x86)) :hints (("Goal" :in-theory (enable ms set-ebp))))

(defthm ms-of-write-byte-to-segment (equal (ms (write-byte-to-segment eff-addr seg-reg val x86)) (ms x86)) :hints (("Goal" :in-theory (enable write-byte-to-segment))))
(defthm ms-of-write-to-segment (equal (ms (write-to-segment n eff-addr seg-reg val x86)) (ms x86)) :hints (("Goal" :in-theory (enable write-to-segment))))


(defthm fault-of-set-reg-high (equal (fault (set-reg-high reg val x86)) (fault x86)) :hints (("Goal" :in-theory (enable fault set-reg-high))))
(defthm fault-of-set-eip (equal (fault (set-eip val x86)) (fault x86)) :hints (("Goal" :in-theory (enable fault set-eip))))
(defthm fault-of-set-eax (equal (fault (set-eax val x86)) (fault x86)) :hints (("Goal" :in-theory (enable fault set-eax))))
(defthm fault-of-set-ebx (equal (fault (set-ebx val x86)) (fault x86)) :hints (("Goal" :in-theory (enable fault set-ebx))))
(defthm fault-of-set-ecx (equal (fault (set-ecx val x86)) (fault x86)) :hints (("Goal" :in-theory (enable fault set-ecx))))
(defthm fault-of-set-edx (equal (fault (set-edx val x86)) (fault x86)) :hints (("Goal" :in-theory (enable fault set-edx))))
;; (defthm fault-of-set-esi (equal (fault (set-esi val x86)) (fault x86)) :hints (("Goal" :in-theory (enable fault set-esi))))
;; (defthm fault-of-set-edi (equal (fault (set-edi val x86)) (fault x86)) :hints (("Goal" :in-theory (enable fault set-edi))))
(defthm fault-of-set-esp (equal (fault (set-esp val x86)) (fault x86)) :hints (("Goal" :in-theory (enable fault set-esp))))
(defthm fault-of-set-ebp (equal (fault (set-ebp val x86)) (fault x86)) :hints (("Goal" :in-theory (enable fault set-ebp))))

(defthm fault-of-write-byte-to-segment (equal (fault (write-byte-to-segment eff-addr seg-reg val x86)) (fault x86)) :hints (("Goal" :in-theory (enable write-byte-to-segment))))
(defthm fault-of-write-to-segment (equal (fault (write-to-segment n eff-addr seg-reg val x86)) (fault x86)) :hints (("Goal" :in-theory (enable write-to-segment))))

(defthm program-at-of-set-reg-high
  (equal (program-at prog-addr bytes (set-reg-high reg val x86))
         (program-at prog-addr bytes x86))
  :hints (("Goal" :in-theory (enable set-reg-high program-at))))

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
