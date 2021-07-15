; An interface to processor flags
;
; Copyright (C) 2019 Kestrel Technology, LLC
; Copyright (C) 2020-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; This book provides a nice interface (set-flag and get-flag) to dealing with x86 processor flags.

(include-book "projects/x86isa/machine/register-readers-and-writers" :dir :system)
(include-book "kestrel/utilities/smaller-termp" :dir :system)
(include-book "kestrel/bv/bvchop" :dir :system)
;(local (include-book "kestrel/arithmetic-light/mod-and-expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod2" :dir :system))


(defconst *flags*
  '(:cf :pf :af :zf :sf :tf :if :df :of :iopl :nt :rf :vm :ac :vif :vip :id))

(defun flag-ok (flag)
  (declare (xargs :guard t))
  (member-eq flag *flags*))

(defun flag-and-val-ok (flag val)
  (declare (xargs :guard t))
  (case flag
    (:cf   (unsigned-byte-p 1 val))
    (:pf   (unsigned-byte-p 1 val))
    (:af   (unsigned-byte-p 1 val))
    (:zf   (unsigned-byte-p 1 val))
    (:sf   (unsigned-byte-p 1 val))
    (:tf   (unsigned-byte-p 1 val))
    (:if   (unsigned-byte-p 1 val))
    (:df   (unsigned-byte-p 1 val))
    (:of   (unsigned-byte-p 1 val))
    (:iopl (unsigned-byte-p 2 val))
    (:nt   (unsigned-byte-p 1 val))
    (:rf   (unsigned-byte-p 1 val))
    (:vm   (unsigned-byte-p 1 val))
    (:ac   (unsigned-byte-p 1 val))
    (:vif  (unsigned-byte-p 1 val))
    (:vip  (unsigned-byte-p 1 val))
    (:id   (unsigned-byte-p 1 val))
    (otherwise nil)))

;; See also !flgi in the mode, but that is a macro and cannot be called with a
;; variable as the flag..
(defund set-flag (flag val x86)
  (declare (xargs :stobjs x86
                  :guard (flag-and-val-ok flag val)))
  (let* ((rflags (rflags x86))
         (new-rflags
          (case flag
            (:cf   (x86isa::!rflagsBits->cf val rflags))
            (:pf   (x86isa::!rflagsBits->pf val rflags))
            (:af   (x86isa::!rflagsBits->af val rflags))
            (:zf   (x86isa::!rflagsBits->zf val rflags))
            (:sf   (x86isa::!rflagsBits->sf val rflags))
            (:tf   (x86isa::!rflagsBits->tf val rflags))
            (:if   (x86isa::!rflagsBits->intf val rflags))
            (:df   (x86isa::!rflagsBits->df val rflags))
            (:of   (x86isa::!rflagsBits->of val rflags))
            (:iopl (x86isa::!rflagsBits->iopl val rflags))
            (:nt   (x86isa::!rflagsBits->nt val rflags))
            (:rf   (x86isa::!rflagsBits->rf val rflags))
            (:vm   (x86isa::!rflagsBits->vm val rflags))
            (:ac   (x86isa::!rflagsBits->ac val rflags))
            (:vif  (x86isa::!rflagsBits->vif val rflags))
            (:vip  (x86isa::!rflagsBits->vip val rflags))
            (:id   (x86isa::!rflagsBits->id val rflags))
            (otherwise (er hard 'set-flag "illegal flag keyword: ~x0.~%" flag)))))
    (!rflags new-rflags x86)))

(defund get-flag (flag x86)
  (declare (xargs :stobjs x86
                  :guard (flag-ok flag)))
  (let ((rflags (rflags x86)))
    (case flag
      (:cf   (x86isa::rflagsBits->cf rflags))
      (:pf   (x86isa::rflagsBits->pf rflags))
      (:af   (x86isa::rflagsBits->af rflags))
      (:zf   (x86isa::rflagsBits->zf rflags))
      (:sf   (x86isa::rflagsBits->sf rflags))
      (:tf   (x86isa::rflagsBits->tf rflags))
      (:if   (x86isa::rflagsBits->intf rflags))
      (:df   (x86isa::rflagsBits->df rflags))
      (:of   (x86isa::rflagsBits->of rflags))
      (:iopl (x86isa::rflagsBits->iopl rflags))
      (:nt   (x86isa::rflagsBits->nt rflags))
      (:rf   (x86isa::rflagsBits->rf rflags))
      (:vm   (x86isa::rflagsBits->vm rflags))
      (:ac   (x86isa::rflagsBits->ac rflags))
      (:vif  (x86isa::rflagsBits->vif rflags))
      (:vip  (x86isa::rflagsBits->vip rflags))
      (:id   (x86isa::rflagsBits->id rflags))
      (otherwise (er hard 'get-flag "illegal flag keyword: ~x0.~%" flag)))))

;;
;; Theorems to introduce get-flag
;;

(defthmd rflagsbits->cf$inline-of-xr
  (equal (x86isa::rflagsbits->cf$inline (xr ':rflags nil x86))
         (get-flag :cf x86))
  :hints (("Goal" :in-theory (enable get-flag))))

(defthmd rflagsbits->pf$inline-of-xr
  (equal (x86isa::rflagsbits->pf$inline (xr ':rflags nil x86))
         (get-flag :pf x86))
  :hints (("Goal" :in-theory (enable get-flag))))

(defthmd rflagsbits->af$inline-of-xr
  (equal (x86isa::rflagsbits->af$inline (xr ':rflags nil x86))
         (get-flag :af x86))
  :hints (("Goal" :in-theory (enable get-flag))))

(defthmd rflagsbits->zf$inline-of-xr
  (equal (x86isa::rflagsbits->zf$inline (xr ':rflags nil x86))
         (get-flag :zf x86))
  :hints (("Goal" :in-theory (enable get-flag))))

(defthmd rflagsbits->sf$inline-of-xr
  (equal (x86isa::rflagsbits->sf$inline (xr ':rflags nil x86))
         (get-flag :sf x86))
  :hints (("Goal" :in-theory (enable get-flag))))

(defthmd rflagsbits->tf$inline-of-xr
  (equal (x86isa::rflagsbits->tf$inline (xr ':rflags nil x86))
         (get-flag :tf x86))
  :hints (("Goal" :in-theory (enable get-flag))))

(defthmd rflagsbits->intf$inline-of-xr
  (equal (x86isa::rflagsbits->intf$inline (xr ':rflags nil x86))
         (get-flag :if x86))
  :hints (("Goal" :in-theory (enable get-flag))))

(defthmd rflagsbits->df$inline-of-xr
  (equal (x86isa::rflagsbits->df$inline (xr ':rflags nil x86))
         (get-flag :df x86))
  :hints (("Goal" :in-theory (enable get-flag))))

(defthmd rflagsbits->of$inline-of-xr
  (equal (x86isa::rflagsbits->of$inline (xr ':rflags nil x86))
         (get-flag :of x86))
  :hints (("Goal" :in-theory (enable get-flag))))

(defthmd rflagsbits->iopl$inline-of-xr
  (equal (x86isa::rflagsbits->iopl$inline (xr ':rflags nil x86))
         (get-flag :iopl x86))
  :hints (("Goal" :in-theory (enable get-flag))))

(defthmd rflagsbits->nt$inline-of-xr
  (equal (x86isa::rflagsbits->nt$inline (xr ':rflags nil x86))
         (get-flag :nt x86))
  :hints (("Goal" :in-theory (enable get-flag))))

(defthmd rflagsbits->rf$inline-of-xr
  (equal (x86isa::rflagsbits->rf$inline (xr ':rflags nil x86))
         (get-flag :rf x86))
  :hints (("Goal" :in-theory (enable get-flag))))

(defthmd rflagsbits->vm$inline-of-xr
  (equal (x86isa::rflagsbits->vm$inline (xr ':rflags nil x86))
         (get-flag :vm x86))
  :hints (("Goal" :in-theory (enable get-flag))))

(defthmd rflagsbits->ac$inline-of-xr
  (equal (x86isa::rflagsbits->ac$inline (xr ':rflags nil x86))
         (get-flag :ac x86))
  :hints (("Goal" :in-theory (enable get-flag))))

(defthmd rflagsbits->vif$inline-of-xr
  (equal (x86isa::rflagsbits->vif$inline (xr ':rflags nil x86))
         (get-flag :vif x86))
  :hints (("Goal" :in-theory (enable get-flag))))

(defthmd rflagsbits->vip$inline-of-xr
  (equal (x86isa::rflagsbits->vip$inline (xr ':rflags nil x86))
         (get-flag :vip x86))
  :hints (("Goal" :in-theory (enable get-flag))))

(defthmd rflagsbits->id$inline-of-xr
  (equal (x86isa::rflagsbits->id$inline (xr ':rflags nil x86))
         (get-flag :id x86))
  :hints (("Goal" :in-theory (enable get-flag))))

;;
;; Theorems to introduce set-flag
;;

(defthmd !rflags-of-!rflagsbits->af
  (equal (x86isa::!rflags (x86isa::!rflagsbits->af$inline val flags) x86)
         (set-flag :af val (x86isa::!rflags flags x86)))
  :hints (("Goal" :in-theory (enable set-flag x86isa::!rflagsbits->af x86isa::rflagsbits-fix))))

(defthmd !rflags-of-!rflagsbits->cf
  (equal (x86isa::!rflags (x86isa::!rflagsbits->cf$inline val flags) x86)
         (set-flag :cf val (x86isa::!rflags flags x86)))
  :hints (("Goal" :in-theory (enable set-flag x86isa::!rflagsbits->cf x86isa::rflagsbits-fix))))

(defthmd !rflags-of-!rflagsbits->pf
  (equal (x86isa::!rflags (x86isa::!rflagsbits->pf$inline val flags) x86)
         (set-flag :pf val (x86isa::!rflags flags x86)))
  :hints (("Goal" :in-theory (enable set-flag x86isa::!rflagsbits->pf x86isa::rflagsbits-fix))))

(defthmd !rflags-of-!rflagsbits->of
  (equal (x86isa::!rflags (x86isa::!rflagsbits->of$inline val flags) x86)
         (set-flag :of val (x86isa::!rflags flags x86)))
  :hints (("Goal" :in-theory (enable set-flag x86isa::!rflagsbits->of x86isa::rflagsbits-fix))))

(defthmd !rflags-of-!rflagsbits->sf
  (equal (x86isa::!rflags (x86isa::!rflagsbits->sf$inline val flags) x86)
         (set-flag :sf val (x86isa::!rflags flags x86)))
  :hints (("Goal" :in-theory (enable set-flag x86isa::!rflagsbits->sf x86isa::rflagsbits-fix))))

(defthmd !rflags-of-!rflagsbits->zf
  (equal (x86isa::!rflags (x86isa::!rflagsbits->zf$inline val flags) x86)
         (set-flag :zf val (x86isa::!rflags flags x86)))
  :hints (("Goal" :in-theory (enable set-flag x86isa::!rflagsbits->zf x86isa::rflagsbits-fix))))



(local (include-book "kestrel/bv/logapp" :dir :system))
(defthm unsigned-byte-p-of-rflagsbits
  (unsigned-byte-p 32 (x86isa::rflagsbits x86isa::cf x86isa::res1
                                          pf x86isa::res2 x86isa::af x86isa::res3
                                          x86isa::zf x86isa::sf x86isa::tf
                                          x86isa::intf x86isa::df x86isa::of
                                          x86isa::iopl x86isa::nt x86isa::res4
                                          x86isa::rf x86isa::vm x86isa::ac
                                          x86isa::vif x86isa::vip id x86isa::res5))
  :hints (("Goal" :in-theory (e/d (X86ISA::RFLAGSBITS) (UNSIGNED-BYTE-P logapp)))))

(defthm get-flag-of-xw
  (implies (not (equal fld :rflags))
           (equal (get-flag flag (xw fld index val x86))
                  (get-flag flag x86)))
  :hints (("Goal" :in-theory (enable get-flag))))

(defthm xr-of-set-flag
  (implies (not (equal fld :rflags))
           (equal (xr fld index (set-flag flag val x86))
                  (xr fld index x86)))
  :hints (("Goal" :in-theory (enable set-flag))))

(defthm set-flag-of-xw
  (implies (not (equal fld :rflags))
           (equal (set-flag flag val1 (xw fld index val2 x86))
                  (xw fld index val2 (set-flag flag val1 x86))))
  :hints (("Goal" :in-theory (enable set-flag))))

;; (local (include-book "kestrel/bv/logand" :dir :system))
;; (local (include-book "kestrel/bv/logior" :dir :system))
;; (defthm logior-combine-constants
;;   (implies (syntaxp (and (quotep i)
;;                          (quotep j)))
;;            (equal (logior i (logior j k))
;;                   (logior (logior i j) k))))

(local (include-book "bitops"))

(defthm set-flag-of-set-flag-same
  (equal (set-flag flag val1 (set-flag flag val2 x86))
         (set-flag flag val1 x86))
  :hints (("Goal" :in-theory (e/d (set-flag
                                   acl2::bfix
                                   x86isa::rflagsBits->ac
                                   x86isa::!rflagsBits->cf
                                   x86isa::!rflagsBits->pf
                                   x86isa::!rflagsBits->af
                                   x86isa::!rflagsBits->zf
                                   x86isa::!rflagsBits->sf
                                   x86isa::!rflagsBits->tf
                                   x86isa::!rflagsBits->intf
                                   x86isa::!rflagsBits->df
                                   x86isa::!rflagsBits->of
                                   x86isa::!rflagsBits->iopl
                                   x86isa::!rflagsBits->nt
                                   x86isa::!rflagsBits->rf
                                   x86isa::!rflagsBits->vm
                                   x86isa::!rflagsBits->ac
                                   x86isa::!rflagsBits->vif
                                   x86isa::!rflagsBits->vip
                                   x86isa::!rflagsBits->id)
                                  (BITOPS::PART-INSTALL-WIDTH-LOW$INLINE)))))

(defthm set-flag-of-set-flag-diff
  (implies (and (syntaxp (and (quotep flag1)
                              (quotep flag2)
                              (acl2::smaller-termp flag2 flag1)))
;                (symbol< flag1 flag2)
                (not (equal flag1 flag2))
                (member-eq flag1 *flags*)
                (member-eq flag2 *flags*)
                )
           (equal (set-flag flag1 val1 (set-flag flag2 val2 x86))
                  (set-flag flag2 val2 (set-flag flag1 val1 x86))))
  :rule-classes ((:rewrite :loop-stopper nil))
  :hints (("Goal" :in-theory (e/d (set-flag
                                   acl2::bfix
                                     x86isa::2bits-fix
                                     x86isa::rflagsBits->ac
                                     x86isa::!rflagsBits->cf
                                     x86isa::!rflagsBits->pf
                                     x86isa::!rflagsBits->af
                                     x86isa::!rflagsBits->zf
                                     x86isa::!rflagsBits->sf
                                     x86isa::!rflagsBits->tf
                                     x86isa::!rflagsBits->intf
                                     x86isa::!rflagsBits->df
                                     x86isa::!rflagsBits->of
                                     x86isa::!rflagsBits->iopl
                                     x86isa::!rflagsBits->nt
                                     x86isa::!rflagsBits->rf
                                     x86isa::!rflagsBits->vm
                                     x86isa::!rflagsBits->ac
                                     x86isa::!rflagsBits->vif
                                     x86isa::!rflagsBits->vip
                                     x86isa::!rflagsBits->id)
                                  (BITOPS::PART-INSTALL-WIDTH-LOW$INLINE)))))

(local (include-book "kestrel/bv/rules10" :dir :system))

(defthm get-flag-of-set-flag
  (implies (and (member-eq flag1 *flags*)
                ;;todo: add more:
                (member-eq flag2 '(:af :cf :pf :of :sf :zf))
                (unsigned-byte-p 1 val))
           (equal (get-flag flag1 (set-flag flag2 val x86))
                  (if (equal flag1 flag2)
                      val
                    (get-flag flag1 x86))))
  :hints (("Goal" :in-theory (enable get-flag
                                     set-flag
                                     X86ISA::!RFLAGSBITS->AF
                                     X86ISA::!RFLAGSBITS->CF
                                     X86ISA::!RFLAGSBITS->PF
                                     X86ISA::!RFLAGSBITS->OF
                                     X86ISA::!RFLAGSBITS->SF
                                     X86ISA::!RFLAGSBITS->ZF

                                     x86isa::rflagsBits->cf
                                     x86isa::rflagsBits->pf
                                     x86isa::rflagsBits->af
                                     x86isa::rflagsBits->zf
                                     x86isa::rflagsBits->sf
                                     x86isa::rflagsBits->tf
                                     x86isa::rflagsBits->intf
                                     x86isa::rflagsBits->df
                                     x86isa::rflagsBits->of
                                     x86isa::rflagsBits->iopl
                                     x86isa::rflagsBits->nt
                                     x86isa::rflagsBits->rf
                                     x86isa::rflagsBits->vm
                                     x86isa::rflagsBits->ac
                                     x86isa::rflagsBits->vif
                                     x86isa::rflagsBits->vip
                                     x86isa::rflagsBits->id

                                     X86ISA::RFLAGSBITS-FIX
                                     ))))

(defthm rflagsbits->cf$inline-of-bvchop-32
  (equal (x86isa::rflagsbits->cf$inline (bvchop 32 rflags))
         (x86isa::rflagsbits->cf$inline rflags))
  :hints (("Goal" :in-theory (enable x86isa::rflagsbits->cf x86isa::rflagsbits-fix))))

(defthm rflagsbits->af$inline-of-bvchop-32
  (equal (x86isa::rflagsbits->af$inline (bvchop 32 rflags))
         (x86isa::rflagsbits->af$inline rflags))
  :hints (("Goal" :in-theory (enable x86isa::rflagsbits->af x86isa::rflagsbits-fix))))

(defthm rflagsbits->pf$inline-of-bvchop-32
  (equal (x86isa::rflagsbits->pf$inline (bvchop 32 rflags))
         (x86isa::rflagsbits->pf$inline rflags))
  :hints (("Goal" :in-theory (enable x86isa::rflagsbits->pf x86isa::rflagsbits-fix))))

(defthm rflagsbits->of$inline-of-bvchop-32
  (equal (x86isa::rflagsbits->of$inline (bvchop 32 rflags))
         (x86isa::rflagsbits->of$inline rflags))
  :hints (("Goal" :in-theory (enable x86isa::rflagsbits->of x86isa::rflagsbits-fix))))

(defthm rflagsbits->sf$inline-of-bvchop-32
  (equal (x86isa::rflagsbits->sf$inline (bvchop 32 rflags))
         (x86isa::rflagsbits->sf$inline rflags))
  :hints (("Goal" :in-theory (enable x86isa::rflagsbits->sf x86isa::rflagsbits-fix))))

(defthm rflagsbits->zf$inline-of-bvchop-32
  (equal (x86isa::rflagsbits->zf$inline (bvchop 32 rflags))
         (x86isa::rflagsbits->zf$inline rflags))
  :hints (("Goal" :in-theory (enable x86isa::rflagsbits->zf x86isa::rflagsbits-fix))))

;;;

(defthm flags-af-af
  (equal (x86isa::rflagsbits->af$inline (x86isa::!rflagsbits->af$inline val rflags))
         (acl2::bfix val))
  :hints (("Goal" :in-theory (enable x86isa::!rflagsbits->af$inline x86isa::rflagsbits->af))))

(defthm flags-cf-cf
  (equal (x86isa::rflagsbits->cf$inline (x86isa::!rflagsbits->cf$inline val rflags))
         (acl2::bfix val))
  :hints (("Goal" :in-theory (enable x86isa::!rflagsbits->cf$inline x86isa::rflagsbits->cf))))

(defthm flags-pf-pf
  (equal (x86isa::rflagsbits->pf$inline (x86isa::!rflagsbits->pf$inline val rflags))
         (acl2::bfix val))
  :hints (("Goal" :in-theory (enable x86isa::!rflagsbits->pf$inline x86isa::rflagsbits->pf))))

(defthm flags-of-of
  (equal (x86isa::rflagsbits->of$inline (x86isa::!rflagsbits->of$inline val rflags))
         (acl2::bfix val))
  :hints (("Goal" :in-theory (enable x86isa::!rflagsbits->of$inline x86isa::rflagsbits->of))))

(defthm flags-sf-sf
  (equal (x86isa::rflagsbits->sf$inline (x86isa::!rflagsbits->sf$inline val rflags))
         (acl2::bfix val))
  :hints (("Goal" :in-theory (enable x86isa::!rflagsbits->sf$inline x86isa::rflagsbits->sf))))

(defthm flags-zf-zf
  (equal (x86isa::rflagsbits->zf$inline (x86isa::!rflagsbits->zf$inline val rflags))
         (acl2::bfix val))
  :hints (("Goal" :in-theory (enable x86isa::!rflagsbits->zf$inline x86isa::rflagsbits->zf))))

;;;


(defthm flags-af-cf
  (equal (x86isa::rflagsbits->af$inline (x86isa::!rflagsbits->cf$inline val rflags))
         (x86isa::rflagsbits->af$inline rflags))
  :hints (("Goal" :in-theory (enable x86isa::!rflagsbits->cf$inline x86isa::rflagsbits->af))))

(defthm flags-af-pf
  (equal (x86isa::rflagsbits->af$inline (x86isa::!rflagsbits->pf$inline val rflags))
         (x86isa::rflagsbits->af$inline rflags))
  :hints (("Goal" :in-theory (enable x86isa::!rflagsbits->pf$inline x86isa::rflagsbits->af))))

(defthm flags-af-of
  (equal (x86isa::rflagsbits->af$inline (x86isa::!rflagsbits->of$inline val rflags))
         (x86isa::rflagsbits->af$inline rflags))
  :hints (("Goal" :in-theory (enable x86isa::!rflagsbits->of$inline x86isa::rflagsbits->af))))

(defthm flags-af-sf
  (equal (x86isa::rflagsbits->af$inline (x86isa::!rflagsbits->sf$inline val rflags))
         (x86isa::rflagsbits->af$inline rflags))
  :hints (("Goal" :in-theory (enable x86isa::!rflagsbits->sf$inline x86isa::rflagsbits->af))))

(defthm flags-af-zf
  (equal (x86isa::rflagsbits->af$inline (x86isa::!rflagsbits->zf$inline val rflags))
         (x86isa::rflagsbits->af$inline rflags))
  :hints (("Goal" :in-theory (enable x86isa::!rflagsbits->zf$inline x86isa::rflagsbits->af))))

;;;

(defthm flags-cf-af
  (equal (x86isa::rflagsbits->cf$inline (x86isa::!rflagsbits->af$inline val rflags))
         (x86isa::rflagsbits->cf$inline rflags))
  :hints (("Goal" :in-theory (enable x86isa::!rflagsbits->af$inline x86isa::rflagsbits->cf))))

(defthm flags-cf-pf
  (equal (x86isa::rflagsbits->cf$inline (x86isa::!rflagsbits->pf$inline val rflags))
         (x86isa::rflagsbits->cf$inline rflags))
  :hints (("Goal" :in-theory (enable x86isa::!rflagsbits->pf$inline x86isa::rflagsbits->cf))))

(defthm flags-cf-of
  (equal (x86isa::rflagsbits->cf$inline (x86isa::!rflagsbits->of$inline val rflags))
         (x86isa::rflagsbits->cf$inline rflags))
  :hints (("Goal" :in-theory (enable x86isa::!rflagsbits->of$inline x86isa::rflagsbits->cf))))

(defthm flags-cf-sf
  (equal (x86isa::rflagsbits->cf$inline (x86isa::!rflagsbits->sf$inline val rflags))
         (x86isa::rflagsbits->cf$inline rflags))
  :hints (("Goal" :in-theory (enable x86isa::!rflagsbits->sf$inline x86isa::rflagsbits->cf))))

(defthm flags-cf-zf
  (equal (x86isa::rflagsbits->cf$inline (x86isa::!rflagsbits->zf$inline val rflags))
         (x86isa::rflagsbits->cf$inline rflags))
  :hints (("Goal" :in-theory (enable x86isa::!rflagsbits->zf$inline x86isa::rflagsbits->cf))))

;;;

(defthm flags-pf-af
  (equal (x86isa::rflagsbits->pf$inline (x86isa::!rflagsbits->af$inline val rflags))
         (x86isa::rflagsbits->pf$inline rflags))
  :hints (("Goal" :in-theory (enable x86isa::!rflagsbits->af$inline x86isa::rflagsbits->pf))))

(defthm flags-pf-cf
  (equal (x86isa::rflagsbits->pf$inline (x86isa::!rflagsbits->cf$inline val rflags))
         (x86isa::rflagsbits->pf$inline rflags))
  :hints (("Goal" :in-theory (enable x86isa::!rflagsbits->cf$inline x86isa::rflagsbits->pf))))

(defthm flags-pf-of
  (equal (x86isa::rflagsbits->pf$inline (x86isa::!rflagsbits->of$inline val rflags))
         (x86isa::rflagsbits->pf$inline rflags))
  :hints (("Goal" :in-theory (enable x86isa::!rflagsbits->of$inline x86isa::rflagsbits->pf))))

(defthm flags-pf-sf
  (equal (x86isa::rflagsbits->pf$inline (x86isa::!rflagsbits->sf$inline val rflags))
         (x86isa::rflagsbits->pf$inline rflags))
  :hints (("Goal" :in-theory (enable x86isa::!rflagsbits->sf$inline x86isa::rflagsbits->pf))))

(defthm flags-pf-zf
  (equal (x86isa::rflagsbits->pf$inline (x86isa::!rflagsbits->zf$inline val rflags))
         (x86isa::rflagsbits->pf$inline rflags))
  :hints (("Goal" :in-theory (enable x86isa::!rflagsbits->zf$inline x86isa::rflagsbits->pf))))

;;;

(defthm flags-of-af
  (equal (x86isa::rflagsbits->of$inline (x86isa::!rflagsbits->af$inline val rflags))
         (x86isa::rflagsbits->of$inline rflags))
  :hints (("Goal" :in-theory (enable x86isa::!rflagsbits->af$inline x86isa::rflagsbits->of))))

(defthm flags-of-cf
  (equal (x86isa::rflagsbits->of$inline (x86isa::!rflagsbits->cf$inline val rflags))
         (x86isa::rflagsbits->of$inline rflags))
  :hints (("Goal" :in-theory (enable x86isa::!rflagsbits->cf$inline x86isa::rflagsbits->of))))

(defthm flags-of-pf
  (equal (x86isa::rflagsbits->of$inline (x86isa::!rflagsbits->pf$inline val rflags))
         (x86isa::rflagsbits->of$inline rflags))
  :hints (("Goal" :in-theory (enable x86isa::!rflagsbits->pf$inline x86isa::rflagsbits->of))))

(defthm flags-of-sf
  (equal (x86isa::rflagsbits->of$inline (x86isa::!rflagsbits->sf$inline val rflags))
         (x86isa::rflagsbits->of$inline rflags))
  :hints (("Goal" :in-theory (enable x86isa::!rflagsbits->sf$inline x86isa::rflagsbits->of))))

(defthm flags-of-zf
  (equal (x86isa::rflagsbits->of$inline (x86isa::!rflagsbits->zf$inline val rflags))
         (x86isa::rflagsbits->of$inline rflags))
  :hints (("Goal" :in-theory (enable x86isa::!rflagsbits->zf$inline x86isa::rflagsbits->of))))

;;;

(defthm flags-sf-af
  (equal (x86isa::rflagsbits->sf$inline (x86isa::!rflagsbits->af$inline val rflags))
         (x86isa::rflagsbits->sf$inline rflags))
  :hints (("Goal" :in-theory (enable x86isa::!rflagsbits->af$inline x86isa::rflagsbits->sf))))

(defthm flags-sf-cf
  (equal (x86isa::rflagsbits->sf$inline (x86isa::!rflagsbits->cf$inline val rflags))
         (x86isa::rflagsbits->sf$inline rflags))
  :hints (("Goal" :in-theory (enable x86isa::!rflagsbits->cf$inline x86isa::rflagsbits->sf))))

(defthm flags-sf-pf
  (equal (x86isa::rflagsbits->sf$inline (x86isa::!rflagsbits->pf$inline val rflags))
         (x86isa::rflagsbits->sf$inline rflags))
  :hints (("Goal" :in-theory (enable x86isa::!rflagsbits->pf$inline x86isa::rflagsbits->sf))))

(defthm flags-sf-of
  (equal (x86isa::rflagsbits->sf$inline (x86isa::!rflagsbits->of$inline val rflags))
         (x86isa::rflagsbits->sf$inline rflags))
  :hints (("Goal" :in-theory (enable x86isa::!rflagsbits->of$inline x86isa::rflagsbits->sf))))

(defthm flags-sf-zf
  (equal (x86isa::rflagsbits->sf$inline (x86isa::!rflagsbits->zf$inline val rflags))
         (x86isa::rflagsbits->sf$inline rflags))
  :hints (("Goal" :in-theory (enable x86isa::!rflagsbits->zf$inline x86isa::rflagsbits->sf))))

;;;

(defthm flags-zf-af
  (equal (x86isa::rflagsbits->zf$inline (x86isa::!rflagsbits->af$inline val rflags))
         (x86isa::rflagsbits->zf$inline rflags))
  :hints (("Goal" :in-theory (enable x86isa::!rflagsbits->af$inline x86isa::rflagsbits->zf))))

(defthm flags-zf-cf
  (equal (x86isa::rflagsbits->zf$inline (x86isa::!rflagsbits->cf$inline val rflags))
         (x86isa::rflagsbits->zf$inline rflags))
  :hints (("Goal" :in-theory (enable x86isa::!rflagsbits->cf$inline x86isa::rflagsbits->zf))))

(defthm flags-zf-pf
  (equal (x86isa::rflagsbits->zf$inline (x86isa::!rflagsbits->pf$inline val rflags))
         (x86isa::rflagsbits->zf$inline rflags))
  :hints (("Goal" :in-theory (enable x86isa::!rflagsbits->pf$inline x86isa::rflagsbits->zf))))

(defthm flags-zf-of
  (equal (x86isa::rflagsbits->zf$inline (x86isa::!rflagsbits->of$inline val rflags))
         (x86isa::rflagsbits->zf$inline rflags))
  :hints (("Goal" :in-theory (enable x86isa::!rflagsbits->of$inline x86isa::rflagsbits->zf))))

(defthm flags-zf-sf
  (equal (x86isa::rflagsbits->zf$inline (x86isa::!rflagsbits->sf$inline val rflags))
         (x86isa::rflagsbits->zf$inline rflags))
  :hints (("Goal" :in-theory (enable x86isa::!rflagsbits->sf$inline x86isa::rflagsbits->zf))))

;;;

(defthm !rflags-of-xr-rflags-of-set-flag
  (implies (member-equal flag '(:af :cf :pf :of :sf :zf))
           (equal (x86isa::!rflags (xr ':rflags nil (set-flag flag val x86)) x86-2)
                  (set-flag flag val (x86isa::!rflags (xr ':rflags nil  x86) x86-2))))
  :hints (("Goal" :in-theory (enable set-flag
                                     x86isa::!rflagsbits->af
                                     x86isa::!rflagsbits->cf
                                     x86isa::!rflagsbits->pf
                                     x86isa::!rflagsbits->of
                                     x86isa::!rflagsbits->sf
                                     x86isa::!rflagsbits->zf
                                     x86isa::rflagsbits-fix))))

(defthm xr-rflags-of-!rflags
  (equal (XR ':RFLAGS NIL (X86ISA::!RFLAGS rflags x86))
         (bvchop 32 rflags))
  :hints (("Goal" :in-theory (enable X86ISA::!RFLAGS))))

(defthm !rflags-of-xw
  (implies (not (equal fld :rflags))
           (equal (x86isa::!rflags rflags (xw fld index val x86))
                  (xw fld index val (x86isa::!rflags rflags x86))))
  :hints (("Goal" :in-theory (enable x86isa::!rflags))))

(defthm !rflags-of-set-flag
  (equal (x86isa::!rflags rflags (set-flag flag val x86))
         (x86isa::!rflags rflags x86))
  :hints (("Goal" :in-theory (enable x86isa::!rflags set-flag))))

(defthm !rflags-of-!rflags
  (equal (x86isa::!rflags rflags (x86isa::!rflags rflags2 x86))
         (x86isa::!rflags rflags x86))
  :hints (("Goal" :in-theory (enable x86isa::!rflags))))

(defthm !rflags-does-nothing
  (implies (and (equal (XR :RFLAGS nil X86)
                       (XR :RFLAGS nil X86-2)
                       )
                (x86p x86-2))
           (equal (X86ISA::!RFLAGS (XR :RFLAGS nil X86) X86-2)
                  x86-2))
  :hints (("Goal" :in-theory (enable x86isa::!rflags ))))

(defthm app-view-of-set-flag
  (equal (app-view (set-flag flag val x86))
         (app-view x86))
  :hints (("Goal" :in-theory (enable set-flag))))

(defthm xr-rflags-of-set-flag-af
  (equal (xr :rflags nil (set-flag :af val x86))
         (x86isa::!rflagsbits->af$inline val (xr :rflags nil x86)))
  :hints (("Goal" :in-theory (enable set-flag))))

(defthm xr-rflags-of-set-flag-cf
  (equal (xr :rflags nil (set-flag :cf val x86))
         (x86isa::!rflagsbits->cf$inline val (xr :rflags nil x86)))
  :hints (("Goal" :in-theory (enable set-flag))))

(defthm xr-rflags-of-set-flag-pf
  (equal (xr :rflags nil (set-flag :pf val x86))
         (x86isa::!rflagsbits->pf$inline val (xr :rflags nil x86)))
  :hints (("Goal" :in-theory (enable set-flag))))

(defthm xr-rflags-of-set-flag-of
  (equal (xr :rflags nil (set-flag :of val x86))
         (x86isa::!rflagsbits->of$inline val (xr :rflags nil x86)))
  :hints (("Goal" :in-theory (enable set-flag))))

(defthm xr-rflags-of-set-flag-sf
  (equal (xr :rflags nil (set-flag :sf val x86))
         (x86isa::!rflagsbits->sf$inline val (xr :rflags nil x86)))
  :hints (("Goal" :in-theory (enable set-flag))))

(defthm xr-rflags-of-set-flag-zf
  (equal (xr :rflags nil (set-flag :zf val x86))
         (x86isa::!rflagsbits->zf$inline val (xr :rflags nil x86)))
  :hints (("Goal" :in-theory (enable set-flag))))

;todo: are there more flags to clear.
;to be left enabled, for now
(defun clear-all-flags (x86)
  (declare (xargs :stobjs x86))
  (let* ((x86 (set-flag :af 0 x86))
         (x86 (set-flag :cf 0 x86))
         (x86 (set-flag :of 0 x86))
         (x86 (set-flag :pf 0 x86))
         (x86 (set-flag :sf 0 x86))
         (x86 (set-flag :zf 0 x86)))
    x86))
