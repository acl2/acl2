; A theory of register readers and writers (emphasis on readability of terms)
;
; Copyright (C) 2016-2019 Kestrel Technology, LLC
; Copyright (C) 2020-2021 Kestrel Institute
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
;(include-book "projects/x86isa/machine/state-field-thms" :dir :system)
(include-book "projects/x86isa/portcullis/sharp-dot-constants" :dir :system)
(include-book "kestrel/bv/bvchop-def" :dir :system)
(local (include-book "kestrel/bv/logext" :dir :system))

(in-theory (disable xw logext))

;; Register readers
(defund eax (x86) (declare (xargs :stobjs x86)) (rgfi *rax* x86))
(defund ebx (x86) (declare (xargs :stobjs x86)) (rgfi *rbx* x86))
(defund ecx (x86) (declare (xargs :stobjs x86)) (rgfi *rcx* x86))
(defund edx (x86) (declare (xargs :stobjs x86)) (rgfi *rdx* x86))
(defund esp (x86) (declare (xargs :stobjs x86)) (rgfi *rsp* x86))
(defund ebp (x86) (declare (xargs :stobjs x86)) (rgfi *rbp* x86))

;; Register writers
(defund set-eax (val x86) (declare (xargs :stobjs x86 :guard (unsigned-byte-p 32 val))) (!rgfi *rax* val x86))
(defund set-ebx (val x86) (declare (xargs :stobjs x86 :guard (unsigned-byte-p 32 val))) (!rgfi *rbx* val x86))
(defund set-ecx (val x86) (declare (xargs :stobjs x86 :guard (unsigned-byte-p 32 val))) (!rgfi *rcx* val x86))
(defund set-edx (val x86) (declare (xargs :stobjs x86 :guard (unsigned-byte-p 32 val))) (!rgfi *rdx* val x86))
(defund set-esp (val x86) (declare (xargs :stobjs x86 :guard (unsigned-byte-p 32 val))) (!rgfi *rsp* val x86))
(defund set-ebp (val x86) (declare (xargs :stobjs x86 :guard (unsigned-byte-p 32 val))) (!rgfi *rbp* val x86))

;; Read of a write of the same register
(defthm eax-of-set-eax (equal (eax (set-eax val x86)) (logext 64 val)) :hints (("Goal" :in-theory (enable eax set-eax))))
(defthm ebx-of-set-ebx (equal (ebx (set-ebx val x86)) (logext 64 val)) :hints (("Goal" :in-theory (enable ebx set-ebx))))
(defthm ecx-of-set-ecx (equal (ecx (set-ecx val x86)) (logext 64 val)) :hints (("Goal" :in-theory (enable ecx set-ecx))))
(defthm edx-of-set-edx (equal (edx (set-edx val x86)) (logext 64 val)) :hints (("Goal" :in-theory (enable edx set-edx))))
(defthm esp-of-set-esp (equal (esp (set-esp val x86)) (logext 64 val)) :hints (("Goal" :in-theory (enable esp set-esp))))
(defthm ebp-of-set-ebp (equal (ebp (set-ebp val x86)) (logext 64 val)) :hints (("Goal" :in-theory (enable ebp set-ebp))))

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

;;;

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

;;;

(defthm set-eax-of-xw
  (implies (or (not (equal fld :rgf))
               ;;(not (equal index *rax*))
               )
           (equal (set-eax eax (xw fld index val x86))
                  (xw fld index val (set-eax eax x86))))
  :hints (("Goal" :in-theory (enable set-eax
                                     ))))

(defthm set-ebx-of-xw
  (implies (or (not (equal fld :rgf))
               ;;(not (equal index *rax*))
               )
           (equal (set-ebx ebx (xw fld index val x86))
                  (xw fld index val (set-ebx ebx x86))))
  :hints (("Goal" :in-theory (enable set-ebx
                                     ))))

(defthm set-ecx-of-xw
  (implies (or (not (equal fld :rgf))
               ;;(not (equal index *rax*))
               )
           (equal (set-ecx ecx (xw fld index val x86))
                  (xw fld index val (set-ecx ecx x86))))
  :hints (("Goal" :in-theory (enable set-ecx
                                     ))))

(defthm set-edx-of-xw
  (implies (or (not (equal fld :rgf))
               ;;(not (equal index *rax*))
               )
           (equal (set-edx edx (xw fld index val x86))
                  (xw fld index val (set-edx edx x86))))
  :hints (("Goal" :in-theory (enable set-edx
                                     ))))

(defthm set-esp-of-xw
  (implies (or (not (equal fld :rgf))
               ;;(not (equal index *rax*))
               )
           (equal (set-esp esp (xw fld index val x86))
                  (xw fld index val (set-esp esp x86))))
  :hints (("Goal" :in-theory (enable set-esp
                                     ))))

(defthm set-ebp-of-xw
  (implies (or (not (equal fld :rgf))
               ;;(not (equal index *rax*))
               )
           (equal (set-ebp ebp (xw fld index val x86))
                  (xw fld index val (set-ebp ebp x86))))
  :hints (("Goal" :in-theory (enable set-ebp
                                     ))))

;;;
;;; sort calls to register writers
;;;

;;; bring set-eax forward

(defthm set-ebx-of-set-eax
  (equal (set-ebx ebx (set-eax eax x86))
         (set-eax eax (set-ebx ebx x86)))
  :hints (("Goal" :in-theory (enable set-eax set-ebx
                                     ))))

(defthm set-ecx-of-set-eax
  (equal (set-ecx ecx (set-eax eax x86))
         (set-eax eax (set-ecx ecx x86)))
  :hints (("Goal" :in-theory (enable set-eax set-ecx
                                     ))))

(defthm set-edx-of-set-eax
  (equal (set-edx edx (set-eax eax x86))
         (set-eax eax (set-edx edx x86)))
  :hints (("Goal" :in-theory (enable set-eax set-edx
                                     ))))

(defthm set-esp-of-set-eax
  (equal (set-esp esp (set-eax eax x86))
         (set-eax eax (set-esp esp x86)))
  :hints (("Goal" :in-theory (enable set-eax set-esp
                                     ))))

(defthm set-ebp-of-set-eax
  (equal (set-ebp ebp (set-eax eax x86))
         (set-eax eax (set-ebp ebp x86)))
  :hints (("Goal" :in-theory (enable set-eax set-ebp
                                     ))))

;;; bring set-ebx forward

(defthm set-ecx-of-set-ebx
  (equal (set-ecx ecx (set-ebx ebx x86))
         (set-ebx ebx (set-ecx ecx x86)))
  :hints (("Goal" :in-theory (enable set-ebx set-ecx
                                     ))))

(defthm set-edx-of-set-ebx
  (equal (set-edx edx (set-ebx ebx x86))
         (set-ebx ebx (set-edx edx x86)))
  :hints (("Goal" :in-theory (enable set-ebx set-edx
                                     ))))

(defthm set-esp-of-set-ebx
  (equal (set-esp esp (set-ebx ebx x86))
         (set-ebx ebx (set-esp esp x86)))
  :hints (("Goal" :in-theory (enable set-ebx set-esp
                                     ))))

(defthm set-ebp-of-set-ebx
  (equal (set-ebp ebp (set-ebx ebx x86))
         (set-ebx ebx (set-ebp ebp x86)))
  :hints (("Goal" :in-theory (enable set-ebx set-ebp
                                     ))))

;;; bring set-ecx forward

(defthm set-edx-of-set-ecx
  (equal (set-edx edx (set-ecx ecx x86))
         (set-ecx ecx (set-edx edx x86)))
  :hints (("Goal" :in-theory (enable set-ecx set-edx
                                     ))))

(defthm set-esp-of-set-ecx
  (equal (set-esp esp (set-ecx ecx x86))
         (set-ecx ecx (set-esp esp x86)))
  :hints (("Goal" :in-theory (enable set-ecx set-esp
                                     ))))

(defthm set-ebp-of-set-ecx
  (equal (set-ebp ebp (set-ecx ecx x86))
         (set-ecx ecx (set-ebp ebp x86)))
  :hints (("Goal" :in-theory (enable set-ecx set-ebp
                                     ))))

;;; bring set-edx forward

(defthm set-esp-of-set-edx
  (equal (set-esp esp (set-edx edx x86))
         (set-edx edx (set-esp esp x86)))
  :hints (("Goal" :in-theory (enable set-edx set-esp
                                     ))))

(defthm set-ebp-of-set-edx
  (equal (set-ebp ebp (set-edx edx x86))
         (set-edx edx (set-ebp ebp x86)))
  :hints (("Goal" :in-theory (enable set-edx set-ebp
                                     ))))

;;; bring set-esp forward

(defthm set-ebp-of-set-esp
  (equal (set-ebp ebp (set-esp esp x86))
         (set-esp esp (set-ebp ebp x86)))
  :hints (("Goal" :in-theory (enable set-esp set-ebp
                                     ))))

;; Write of write of the same register
(defthm set-eax-of-set-eax (equal (set-eax eax1 (set-eax eax2 x86)) (set-eax eax1 x86)) :hints (("Goal" :in-theory (enable set-eax))))
(defthm set-ebx-of-set-ebx (equal (set-ebx ebx1 (set-ebx ebx2 x86)) (set-ebx ebx1 x86)) :hints (("Goal" :in-theory (enable set-ebx))))
(defthm set-ecx-of-set-ecx (equal (set-ecx ecx1 (set-ecx ecx2 x86)) (set-ecx ecx1 x86)) :hints (("Goal" :in-theory (enable set-ecx))))
(defthm set-edx-of-set-edx (equal (set-edx edx1 (set-edx edx2 x86)) (set-edx edx1 x86)) :hints (("Goal" :in-theory (enable set-edx))))
(defthm set-esp-of-set-esp (equal (set-esp esp1 (set-esp esp2 x86)) (set-esp esp1 x86)) :hints (("Goal" :in-theory (enable set-esp))))
(defthm set-ebp-of-set-ebp (equal (set-ebp ebp1 (set-ebp ebp2 x86)) (set-ebp ebp1 x86)) :hints (("Goal" :in-theory (enable set-ebp))))

;; Introduce the register writers:
(defthmd xw-becomes-set-eax (equal (xw :rgf *rax* val x86) (set-eax val x86)) :hints (("Goal" :in-theory (enable set-eax))))
(defthmd xw-becomes-set-ebx (equal (xw :rgf *rbx* val x86) (set-ebx val x86)) :hints (("Goal" :in-theory (enable set-ebx))))
(defthmd xw-becomes-set-ecx (equal (xw :rgf *rcx* val x86) (set-ecx val x86)) :hints (("Goal" :in-theory (enable set-ecx))))
(defthmd xw-becomes-set-edx (equal (xw :rgf *rdx* val x86) (set-edx val x86)) :hints (("Goal" :in-theory (enable set-edx))))
(defthmd xw-becomes-set-esp (equal (xw :rgf *rsp* val x86) (set-esp val x86)) :hints (("Goal" :in-theory (enable set-esp))))
(defthmd xw-becomes-set-ebp (equal (xw :rgf *rbp* val x86) (set-ebp val x86)) :hints (("Goal" :in-theory (enable set-ebp))))

;; These rules are disabled since they are not appropriate for 64-bit reasoning:
(theory-invariant (incompatible (:definition set-eax) (:rewrite xw-becomes-set-eax)))
(theory-invariant (incompatible (:definition set-ebx) (:rewrite xw-becomes-set-ebx)))
(theory-invariant (incompatible (:definition set-ecx) (:rewrite xw-becomes-set-ecx)))
(theory-invariant (incompatible (:definition set-edx) (:rewrite xw-becomes-set-edx)))
(theory-invariant (incompatible (:definition set-esp) (:rewrite xw-becomes-set-esp)))
(theory-invariant (incompatible (:definition set-ebp) (:rewrite xw-becomes-set-ebp)))

;; Introduce the register readers:
(defthmd xr-becomes-eax (equal (xr :rgf *rax* x86) (eax x86)) :hints (("Goal" :in-theory (enable eax))))
(defthmd xr-becomes-ebx (equal (xr :rgf *rbx* x86) (ebx x86)) :hints (("Goal" :in-theory (enable ebx))))
(defthmd xr-becomes-ecx (equal (xr :rgf *rcx* x86) (ecx x86)) :hints (("Goal" :in-theory (enable ecx))))
(defthmd xr-becomes-edx (equal (xr :rgf *rdx* x86) (edx x86)) :hints (("Goal" :in-theory (enable edx))))
(defthmd xr-becomes-esp (equal (xr :rgf *rsp* x86) (esp x86)) :hints (("Goal" :in-theory (enable esp))))
(defthmd xr-becomes-ebp (equal (xr :rgf *rbp* x86) (ebp x86)) :hints (("Goal" :in-theory (enable ebp))))

;; These rules are disabled since they are not appropriate for 64-bit reasoning:
(theory-invariant (incompatible (:definition eax) (:rewrite xr-becomes-eax)))
(theory-invariant (incompatible (:definition ebx) (:rewrite xr-becomes-ebx)))
(theory-invariant (incompatible (:definition ecx) (:rewrite xr-becomes-ecx)))
(theory-invariant (incompatible (:definition edx) (:rewrite xr-becomes-edx)))
(theory-invariant (incompatible (:definition esp) (:rewrite xr-becomes-esp)))
(theory-invariant (incompatible (:definition ebp) (:rewrite xr-becomes-ebp)))

;;; todo: can we get rid of these?

(defthm xr-of-set-esp-same
  (equal (xr ':rgf '4 (set-esp esp x86))
         (logext 64 esp))
  :hints (("Goal" :in-theory (enable set-esp))))

(defthm xr-of-esp-and-set-eax
  (equal (xr ':rgf '4 (set-eax esp x86))
         (xr ':rgf '4 x86))
  :hints (("Goal" :in-theory (enable set-eax))))

(defthm xr-of-esp-and-set-ebx
  (equal (xr ':rgf '4 (set-ebx esp x86))
         (xr ':rgf '4 x86))
  :hints (("Goal" :in-theory (enable set-ebx))))

(defthm xr-of-esp-and-set-ecx
  (equal (xr ':rgf '4 (set-ecx esp x86))
         (xr ':rgf '4 x86))
  :hints (("Goal" :in-theory (enable set-ecx))))

(defthm xr-of-esp-and-set-edx
  (equal (xr ':rgf '4 (set-edx esp x86))
         (xr ':rgf '4 x86))
  :hints (("Goal" :in-theory (enable set-edx))))

(defthm xr-of-esp-and-set-ebp
  (equal (xr ':rgf '4 (set-ebp ebp x86))
         (xr ':rgf '4 x86))
  :hints (("Goal" :in-theory (enable set-ebp))))

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
