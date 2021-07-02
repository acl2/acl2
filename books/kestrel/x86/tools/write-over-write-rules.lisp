; "Write over write" rules for our x86 state writers
;
; Copyright (C) 2016-2019 Kestrel Technology, LLC
; Copyright (C) 2020-2021 Kestrel Institute
;;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

(include-book "support32")
(include-book "register-readers-and-writers")

(defthm write-byte-to-segment-of-set-eip
  (equal (write-byte-to-segment eff-addr seg-reg val (set-eip eip x86))
         (set-eip eip (write-byte-to-segment eff-addr seg-reg val x86)))
  :hints (("Goal" :in-theory (enable write-byte-to-segment))))

(defthm write-to-segment-of-set-eip
  (equal (write-to-segment n eff-addr seg-reg val (set-eip eip x86))
         (set-eip eip  (write-to-segment n eff-addr seg-reg val x86)))
  :hints (("Goal" :in-theory (enable write-to-segment))))




(defthm set-flag-of-write-byte-to-segment
  (equal (set-flag flag fval (write-byte-to-segment eff-addr seg-reg val x86))
         (write-byte-to-segment eff-addr seg-reg val (set-flag flag fval x86)))
  :hints (("Goal" :in-theory (enable write-byte-to-segment))))

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
  :hints (("Goal" :in-theory (e/d (write-byte-to-segment set-eax) ()))))

(defthm write-byte-to-segment-of-set-ebx
  (equal (write-byte-to-segment eff-addr seg-reg val (set-ebx ebx x86))
         (set-ebx ebx (write-byte-to-segment eff-addr seg-reg val x86)))
  :hints (("Goal" :in-theory (e/d (write-byte-to-segment set-ebx) ()))))

(defthm write-byte-to-segment-of-set-ecx
  (equal (write-byte-to-segment eff-addr seg-reg val (set-ecx ecx x86))
         (set-ecx ecx (write-byte-to-segment eff-addr seg-reg val x86)))
  :hints (("Goal" :in-theory (e/d (write-byte-to-segment set-ecx) ()))))

(defthm write-byte-to-segment-of-set-edx
  (equal (write-byte-to-segment eff-addr seg-reg val (set-edx edx x86))
         (set-edx edx (write-byte-to-segment eff-addr seg-reg val x86)))
  :hints (("Goal" :in-theory (e/d (write-byte-to-segment set-edx) ()))))

(defthm write-byte-to-segment-of-set-esp
  (equal (write-byte-to-segment eff-addr seg-reg val (set-esp esp x86))
         (set-esp esp (write-byte-to-segment eff-addr seg-reg val x86)))
  :hints (("Goal" :in-theory (e/d (write-byte-to-segment set-esp) ()))))

(defthm write-byte-to-segment-of-set-ebp
  (equal (write-byte-to-segment eff-addr seg-reg val (set-ebp ebp x86))
         (set-ebp ebp (write-byte-to-segment eff-addr seg-reg val x86)))
  :hints (("Goal" :in-theory (e/d (write-byte-to-segment set-ebp) ()))))

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
