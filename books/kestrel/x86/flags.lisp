; An interface to processor flags
;
; Copyright (C) 2019 Kestrel Technology, LLC
; Copyright (C) 2020-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; This book provides a nice interface (set-flag and get-flag) to dealing with x86 processor flags.

(include-book "projects/x86isa/machine/state" :dir :system)
;(include-book "projects/x86isa/machine/register-readers-and-writers" :dir :system)
(include-book "kestrel/utilities/smaller-termp" :dir :system)
(include-book "kestrel/bv/bvchop" :dir :system)
(include-book "kestrel/bv/trim-intro-rules" :dir :system)
;(local (include-book "kestrel/arithmetic-light/mod-and-expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod2" :dir :system))
(local (include-book "kestrel/bv/rules" :dir :system)) ; to tighten a bvcat?
(local (include-book "kestrel/bv/slice" :dir :system))
(local (include-book "kestrel/bv/bitops" :dir :system))

(set-compile-fns t) ; Matt K. mod for GCL to avoid exhausting storage

(defthm !rflags-of-if-arg1
  (equal (!rflags (if test v1 v2) x86)
         (if test (!rflags v1 x86) (!rflags v2 x86))))

(defthm !rflags-of-if-arg2
  (equal (!rflags v (if test x86_1 x86_2))
         (if test (!rflags v x86_1) (!rflags v x86_2))))

(defconst *flags*
  '(:cf :pf :af :zf :sf :tf :if :df :of :iopl :nt :rf :vm :ac :vif :vip :id))

(defconst *one-bit-flags*
  '(:cf :pf :af :zf :sf :tf :if :df :of
        ;; :iopl
        :nt :rf :vm :ac :vif :vip :id))

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

;; See also !flgi in the model, but that is a macro and cannot be called with a
;; variable as the flag..
(defund set-flag (flag val x86)
  (declare (xargs :guard (flag-and-val-ok flag val)
                  :stobjs x86))
  (let* ((rflags (rflags x86))
         (new-rflags
          (case flag
            (:cf   (!rflagsbits->cf   val rflags))
            (:pf   (!rflagsbits->pf   val rflags))
            (:af   (!rflagsbits->af   val rflags))
            (:zf   (!rflagsbits->zf   val rflags))
            (:sf   (!rflagsbits->sf   val rflags))
            (:tf   (!rflagsbits->tf   val rflags))
            (:if   (!rflagsbits->intf val rflags)) ; note mismatch between :if and "intf" -- maybe to avoid the name "if"
            (:df   (!rflagsbits->df   val rflags))
            (:of   (!rflagsbits->of   val rflags))
            (:iopl (!rflagsbits->iopl val rflags))
            (:nt   (!rflagsbits->nt   val rflags))
            (:rf   (!rflagsbits->rf   val rflags))
            (:vm   (!rflagsbits->vm   val rflags))
            (:ac   (!rflagsbits->ac   val rflags))
            (:vif  (!rflagsbits->vif  val rflags))
            (:vip  (!rflagsbits->vip  val rflags))
            (:id   (!rflagsbits->id   val rflags))
            (otherwise (er hard 'set-flag "illegal flag keyword: ~x0.~%" flag)))))
    (!rflags new-rflags x86)))

(defund get-flag (flag x86)
  (declare (xargs :guard (flag-ok flag)
                  :stobjs x86))
  (let ((rflags (rflags x86)))
    (case flag
      (:cf   (rflagsbits->cf   rflags))
      (:pf   (rflagsbits->pf   rflags))
      (:af   (rflagsbits->af   rflags))
      (:zf   (rflagsbits->zf   rflags))
      (:sf   (rflagsbits->sf   rflags))
      (:tf   (rflagsbits->tf   rflags))
      (:if   (rflagsbits->intf rflags)) ; see above note on name mismatch
      (:df   (rflagsbits->df   rflags))
      (:of   (rflagsbits->of   rflags))
      (:iopl (rflagsbits->iopl rflags))
      (:nt   (rflagsbits->nt   rflags))
      (:rf   (rflagsbits->rf   rflags))
      (:vm   (rflagsbits->vm   rflags))
      (:ac   (rflagsbits->ac   rflags))
      (:vif  (rflagsbits->vif  rflags))
      (:vip  (rflagsbits->vip  rflags))
      (:id   (rflagsbits->id   rflags))
      (otherwise (er hard 'get-flag "illegal flag keyword: ~x0.~%" flag)))))

;; for any of the *one-bit-flags*
(defthm unsigned-byte-p-of-get-flag-one-bit
  (implies (and (member-eq flag *one-bit-flags*)
                (posp size))
           (unsigned-byte-p size (get-flag flag x86)))
  :hints (("Goal" :in-theory (enable get-flag))))

;;
;; Rules to introduce get-flag
;;

(defthmd rflagsbits->cf$inline-of-xr
  (equal (rflagsbits->cf$inline (xr :rflags nil x86))
         (get-flag :cf x86))
  :hints (("Goal" :in-theory (enable get-flag))))

(defthmd rflagsbits->pf$inline-of-xr
  (equal (rflagsbits->pf$inline (xr :rflags nil x86))
         (get-flag :pf x86))
  :hints (("Goal" :in-theory (enable get-flag))))

(defthmd rflagsbits->af$inline-of-xr
  (equal (rflagsbits->af$inline (xr :rflags nil x86))
         (get-flag :af x86))
  :hints (("Goal" :in-theory (enable get-flag))))

(defthmd rflagsbits->zf$inline-of-xr
  (equal (rflagsbits->zf$inline (xr :rflags nil x86))
         (get-flag :zf x86))
  :hints (("Goal" :in-theory (enable get-flag))))

(defthmd rflagsbits->sf$inline-of-xr
  (equal (rflagsbits->sf$inline (xr :rflags nil x86))
         (get-flag :sf x86))
  :hints (("Goal" :in-theory (enable get-flag))))

(defthmd rflagsbits->tf$inline-of-xr
  (equal (rflagsbits->tf$inline (xr :rflags nil x86))
         (get-flag :tf x86))
  :hints (("Goal" :in-theory (enable get-flag))))

(defthmd rflagsbits->intf$inline-of-xr
  (equal (rflagsbits->intf$inline (xr :rflags nil x86))
         (get-flag :if x86))
  :hints (("Goal" :in-theory (enable get-flag))))

(defthmd rflagsbits->df$inline-of-xr
  (equal (rflagsbits->df$inline (xr :rflags nil x86))
         (get-flag :df x86))
  :hints (("Goal" :in-theory (enable get-flag))))

(defthmd rflagsbits->of$inline-of-xr
  (equal (rflagsbits->of$inline (xr :rflags nil x86))
         (get-flag :of x86))
  :hints (("Goal" :in-theory (enable get-flag))))

(defthmd rflagsbits->iopl$inline-of-xr
  (equal (rflagsbits->iopl$inline (xr :rflags nil x86))
         (get-flag :iopl x86))
  :hints (("Goal" :in-theory (enable get-flag))))

(defthmd rflagsbits->nt$inline-of-xr
  (equal (rflagsbits->nt$inline (xr :rflags nil x86))
         (get-flag :nt x86))
  :hints (("Goal" :in-theory (enable get-flag))))

(defthmd rflagsbits->rf$inline-of-xr
  (equal (rflagsbits->rf$inline (xr :rflags nil x86))
         (get-flag :rf x86))
  :hints (("Goal" :in-theory (enable get-flag))))

(defthmd rflagsbits->vm$inline-of-xr
  (equal (rflagsbits->vm$inline (xr :rflags nil x86))
         (get-flag :vm x86))
  :hints (("Goal" :in-theory (enable get-flag))))

(defthmd rflagsbits->ac$inline-of-xr
  (equal (rflagsbits->ac$inline (xr :rflags nil x86))
         (get-flag :ac x86))
  :hints (("Goal" :in-theory (enable get-flag))))

(defthmd rflagsbits->vif$inline-of-xr
  (equal (rflagsbits->vif$inline (xr :rflags nil x86))
         (get-flag :vif x86))
  :hints (("Goal" :in-theory (enable get-flag))))

(defthmd rflagsbits->vip$inline-of-xr
  (equal (rflagsbits->vip$inline (xr :rflags nil x86))
         (get-flag :vip x86))
  :hints (("Goal" :in-theory (enable get-flag))))

(defthmd rflagsbits->id$inline-of-xr
  (equal (rflagsbits->id$inline (xr :rflags nil x86))
         (get-flag :id x86))
  :hints (("Goal" :in-theory (enable get-flag))))

;;
;; Rules to introduce set-flag
;;

(defthmd !rflags-of-!rflagsbits->af
  (equal (!rflags (!rflagsbits->af val flags) x86)
         (set-flag :af val (!rflags flags x86)))
  :hints (("Goal" :in-theory (enable set-flag !rflagsbits->af rflagsbits-fix))))

(defthmd !rflags-of-!rflagsbits->cf
  (equal (!rflags (!rflagsbits->cf val flags) x86)
         (set-flag :cf val (!rflags flags x86)))
  :hints (("Goal" :in-theory (enable set-flag !rflagsbits->cf rflagsbits-fix))))

(defthmd !rflags-of-!rflagsbits->pf
  (equal (!rflags (!rflagsbits->pf val flags) x86)
         (set-flag :pf val (!rflags flags x86)))
  :hints (("Goal" :in-theory (enable set-flag !rflagsbits->pf rflagsbits-fix))))

(defthmd !rflags-of-!rflagsbits->of
  (equal (!rflags (!rflagsbits->of val flags) x86)
         (set-flag :of val (!rflags flags x86)))
  :hints (("Goal" :in-theory (enable set-flag !rflagsbits->of rflagsbits-fix))))

(defthmd !rflags-of-!rflagsbits->sf
  (equal (!rflags (!rflagsbits->sf val flags) x86)
         (set-flag :sf val (!rflags flags x86)))
  :hints (("Goal" :in-theory (enable set-flag !rflagsbits->sf rflagsbits-fix))))

(defthmd !rflags-of-!rflagsbits->zf
  (equal (!rflags (!rflagsbits->zf val flags) x86)
         (set-flag :zf val (!rflags flags x86)))
  :hints (("Goal" :in-theory (enable set-flag !rflagsbits->zf rflagsbits-fix))))



(local (include-book "kestrel/bv/logapp" :dir :system))
(defthm unsigned-byte-p-of-rflagsbits
  (unsigned-byte-p 32 (rflagsbits cf res1 pf res2 af res3 zf sf tf intf df of iopl nt res4 rf vm ac vif vip id res5))
  :hints (("Goal" :in-theory (e/d (rflagsbits) (unsigned-byte-p logapp)))))

(defthm get-flag-of-if
  (equal (get-flag flag (if test x86 x86_2))
         (if test (get-flag flag x86) (get-flag flag x86_2))))

(defthm get-flag-of-xw
  (implies (not (equal fld :rflags))
           (equal (get-flag flag (xw fld index val x86))
                  (get-flag flag x86)))
  :hints (("Goal" :in-theory (enable get-flag))))

(defthm get-flag-of-!memi
  (equal (get-flag flg (!memi i v x86))
         (get-flag flg x86))
  :hints (("Goal" :in-theory (enable !memi))))

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

(defthm set-flag-of-set-flag-same
  (equal (set-flag flag val1 (set-flag flag val2 x86))
         (set-flag flag val1 x86))
  :hints (("Goal" :in-theory (e/d (set-flag
                                   acl2::bfix
                                   ;rflagsbits->ac
                                   !rflagsbits->cf
                                   !rflagsbits->pf
                                   !rflagsbits->af
                                   !rflagsbits->zf
                                   !rflagsbits->sf
                                   !rflagsbits->tf
                                   !rflagsbits->intf
                                   !rflagsbits->df
                                   !rflagsbits->of
                                   !rflagsbits->iopl
                                   !rflagsbits->nt
                                   !rflagsbits->rf
                                   !rflagsbits->vm
                                   !rflagsbits->ac
                                   !rflagsbits->vif
                                   !rflagsbits->vip
                                   !rflagsbits->id)
                                  (part-install-width-low$inline)))))

(defthm set-flag-of-set-flag-diff
  (implies (and (syntaxp (and (quotep flag1)
                              (quotep flag2)
                              (acl2::smaller-termp flag2 flag1)))
                ;; (symbol< flag1 flag2)
                (not (equal flag1 flag2)) ; gets computed
                (member-eq flag1 *flags*) ; gets computed
                (member-eq flag2 *flags*) ; gets computed
                )
           (equal (set-flag flag1 val1 (set-flag flag2 val2 x86))
                  (set-flag flag2 val2 (set-flag flag1 val1 x86))))
  :rule-classes ((:rewrite :loop-stopper nil))
  :hints (("Goal" :in-theory (e/d (set-flag
                                   acl2::bfix
                                   2bits-fix
                                   ;rflagsbits->ac
                                   !rflagsbits->cf
                                   !rflagsbits->pf
                                   !rflagsbits->af
                                   !rflagsbits->zf
                                   !rflagsbits->sf
                                   !rflagsbits->tf
                                   !rflagsbits->intf
                                   !rflagsbits->df
                                   !rflagsbits->of
                                   !rflagsbits->iopl
                                   !rflagsbits->nt
                                   !rflagsbits->rf
                                   !rflagsbits->vm
                                   !rflagsbits->ac
                                   !rflagsbits->vif
                                   !rflagsbits->vip
                                   !rflagsbits->id)
                                  (part-install-width-low$inline)))))

(local (include-book "kestrel/bv/rules10" :dir :system))

(defthm get-flag-of-set-flag
  (implies (and (member-eq flag1 *flags*)
                ;;todo: add more:
                (member-eq flag2 *one-bit-flags*))
           (equal (get-flag flag1 (set-flag flag2 val x86))
                  (if (equal flag1 flag2)
                      (acl2::bfix val)
                    (get-flag flag1 x86))))
  :hints (("Goal" :in-theory (enable get-flag
                                     set-flag
                                     !rflagsbits->af
                                     !rflagsbits->cf
                                     !rflagsbits->pf
                                     !rflagsbits->of
                                     !rflagsbits->sf
                                     !rflagsbits->zf
                                     !rflagsbits->tf
                                     !rflagsbits->intf
                                     !rflagsbits->df
                                     !rflagsbits->of
                                     !rflagsbits->iopl
                                     !rflagsbits->nt
                                     !rflagsbits->rf
                                     !rflagsbits->vm
                                     !rflagsbits->ac
                                     !rflagsbits->vif
                                     !rflagsbits->vip
                                     !rflagsbits->id
                                     rflagsbits->cf
                                     rflagsbits->pf
                                     rflagsbits->af
                                     rflagsbits->zf
                                     rflagsbits->sf
                                     rflagsbits->tf
                                     rflagsbits->intf
                                     rflagsbits->df
                                     rflagsbits->of
                                     rflagsbits->iopl
                                     rflagsbits->nt
                                     rflagsbits->rf
                                     rflagsbits->vm
                                     rflagsbits->ac
                                     rflagsbits->vif
                                     rflagsbits->vip
                                     rflagsbits->id
                                     rflagsbits-fix))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm rflagsbits->cf$inline-of-bvchop-32
  (equal (rflagsbits->cf$inline (bvchop 32 rflags))
         (rflagsbits->cf$inline rflags))
  :hints (("Goal" :in-theory (enable rflagsbits->cf rflagsbits-fix))))

(defthm rflagsbits->res1-of-bvchop-32
  (equal (rflagsbits->res1 (bvchop 32 input-rflags))
         (rflagsbits->res1 input-rflags))
  :hints (("Goal" :in-theory (enable rflagsbits->res1 rflagsbits-fix))))

(defthm rflagsbits->pf$inline-of-bvchop-32
  (equal (rflagsbits->pf$inline (bvchop 32 rflags))
         (rflagsbits->pf$inline rflags))
  :hints (("Goal" :in-theory (enable rflagsbits->pf rflagsbits-fix))))

(defthm rflagsbits->res2-of-bvchop-32
  (equal (rflagsbits->res2 (bvchop 32 input-rflags))
         (rflagsbits->res2 input-rflags))
  :hints (("Goal" :in-theory (enable rflagsbits->res2 rflagsbits-fix))))

(defthm rflagsbits->af$inline-of-bvchop-32
  (equal (rflagsbits->af$inline (bvchop 32 rflags))
         (rflagsbits->af$inline rflags))
  :hints (("Goal" :in-theory (enable rflagsbits->af rflagsbits-fix))))

(defthm rflagsbits->res3-of-bvchop-32
  (equal (rflagsbits->res3 (bvchop 32 input-rflags))
         (rflagsbits->res3 input-rflags))
  :hints (("Goal" :in-theory (enable rflagsbits->res3 rflagsbits-fix))))

(defthm rflagsbits->zf$inline-of-bvchop-32
  (equal (rflagsbits->zf$inline (bvchop 32 rflags))
         (rflagsbits->zf$inline rflags))
  :hints (("Goal" :in-theory (enable rflagsbits->zf rflagsbits-fix))))

(defthm rflagsbits->sf$inline-of-bvchop-32
  (equal (rflagsbits->sf$inline (bvchop 32 rflags))
         (rflagsbits->sf$inline rflags))
  :hints (("Goal" :in-theory (enable rflagsbits->sf rflagsbits-fix))))

(defthm rflagsbits->tf-of-bvchop-32
  (equal (rflagsbits->tf (bvchop 32 input-rflags))
         (rflagsbits->tf input-rflags))
  :hints (("Goal" :in-theory (enable rflagsbits->tf rflagsbits-fix))))

(defthm intflagsbits->intf-of-bvchop-32
  (equal (rflagsbits->intf (bvchop 32 input-rflags))
         (rflagsbits->intf input-rflags))
  :hints (("Goal" :in-theory (enable rflagsbits->intf rflagsbits-fix))))

(defthm rflagsbits->df-of-bvchop-32
  (equal (rflagsbits->df (bvchop 32 input-rflags))
         (rflagsbits->df input-rflags))
  :hints (("Goal" :in-theory (enable rflagsbits->df rflagsbits-fix))))

(defthm rflagsbits->of$inline-of-bvchop-32
  (equal (rflagsbits->of$inline (bvchop 32 rflags))
         (rflagsbits->of$inline rflags))
  :hints (("Goal" :in-theory (enable rflagsbits->of rflagsbits-fix))))

(defthm rflagsbits->iopl-of-bvchop-32
  (equal (rflagsbits->iopl (bvchop 32 input-rflags))
         (rflagsbits->iopl input-rflags))
  :hints (("Goal" :in-theory (enable rflagsbits->iopl rflagsbits-fix))))

(defthm rflagsbits->nt-of-bvchop-32
  (equal (rflagsbits->nt (bvchop 32 input-rflags))
         (rflagsbits->nt input-rflags))
  :hints (("Goal" :in-theory (enable rflagsbits->nt rflagsbits-fix))))

(defthm rflagsbits->res4-of-bvchop-32
  (equal (rflagsbits->res4 (bvchop 32 input-rflags))
         (rflagsbits->res4 input-rflags))
  :hints (("Goal" :in-theory (enable rflagsbits->res4 rflagsbits-fix))))

(defthm rflagsbits->rf-of-bvchop-32
  (equal (rflagsbits->rf (bvchop 32 input-rflags))
         (rflagsbits->rf input-rflags))
  :hints (("Goal" :in-theory (enable rflagsbits->rf rflagsbits-fix))))

(defthm rflagsbits->vm-of-bvchop-32
  (equal (rflagsbits->vm (bvchop 32 input-rflags))
         (rflagsbits->vm input-rflags))
  :hints (("Goal" :in-theory (enable rflagsbits->vm rflagsbits-fix))))

(defthm rflagsbits->ac-of-bvchop-32
  (equal (rflagsbits->ac (bvchop 32 input-rflags))
         (rflagsbits->ac input-rflags))
  :hints (("Goal" :in-theory (enable rflagsbits->ac rflagsbits-fix))))

(defthm rflagsbits->vif-of-bvchop-32
  (equal (rflagsbits->vif (bvchop 32 input-rflags))
         (rflagsbits->vif input-rflags))
  :hints (("Goal" :in-theory (enable rflagsbits->vif rflagsbits-fix))))

(defthm rflagsbits->vip-of-bvchop-32
  (equal (rflagsbits->vip (bvchop 32 input-rflags))
         (rflagsbits->vip input-rflags))
  :hints (("Goal" :in-theory (enable rflagsbits->vip rflagsbits-fix))))

(defthm rflagsbits->id-of-bvchop-32
  (equal (rflagsbits->id (bvchop 32 input-rflags))
         (rflagsbits->id input-rflags))
  :hints (("Goal" :in-theory (enable rflagsbits->id rflagsbits-fix))))

(defthm rflagsbits->res5-of-bvchop-32
  (equal (rflagsbits->res5 (bvchop 32 input-rflags))
         (rflagsbits->res5 input-rflags))
  :hints (("Goal" :in-theory (enable rflagsbits->res5 rflagsbits-fix))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; todo: rename all of these:

(defthm flags-af-af
  (equal (rflagsbits->af$inline (!rflagsbits->af$inline val rflags))
         (acl2::bfix val))
  :hints (("Goal" :in-theory (enable !rflagsbits->af$inline rflagsbits->af))))

(defthm flags-cf-cf
  (equal (rflagsbits->cf$inline (!rflagsbits->cf$inline val rflags))
         (acl2::bfix val))
  :hints (("Goal" :in-theory (enable !rflagsbits->cf$inline rflagsbits->cf))))

(defthm flags-pf-pf
  (equal (rflagsbits->pf$inline (!rflagsbits->pf$inline val rflags))
         (acl2::bfix val))
  :hints (("Goal" :in-theory (enable !rflagsbits->pf$inline rflagsbits->pf))))

(defthm flags-of-of
  (equal (rflagsbits->of$inline (!rflagsbits->of$inline val rflags))
         (acl2::bfix val))
  :hints (("Goal" :in-theory (enable !rflagsbits->of$inline rflagsbits->of))))

(defthm flags-sf-sf
  (equal (rflagsbits->sf$inline (!rflagsbits->sf$inline val rflags))
         (acl2::bfix val))
  :hints (("Goal" :in-theory (enable !rflagsbits->sf$inline rflagsbits->sf))))

(defthm flags-zf-zf
  (equal (rflagsbits->zf$inline (!rflagsbits->zf$inline val rflags))
         (acl2::bfix val))
  :hints (("Goal" :in-theory (enable !rflagsbits->zf$inline rflagsbits->zf))))

;;;


(defthm flags-af-cf
  (equal (rflagsbits->af$inline (!rflagsbits->cf$inline val rflags))
         (rflagsbits->af$inline rflags))
  :hints (("Goal" :in-theory (enable !rflagsbits->cf$inline rflagsbits->af))))

(defthm flags-af-pf
  (equal (rflagsbits->af$inline (!rflagsbits->pf$inline val rflags))
         (rflagsbits->af$inline rflags))
  :hints (("Goal" :in-theory (enable !rflagsbits->pf$inline rflagsbits->af))))

(defthm flags-af-of
  (equal (rflagsbits->af$inline (!rflagsbits->of$inline val rflags))
         (rflagsbits->af$inline rflags))
  :hints (("Goal" :in-theory (enable !rflagsbits->of$inline rflagsbits->af))))

(defthm flags-af-sf
  (equal (rflagsbits->af$inline (!rflagsbits->sf$inline val rflags))
         (rflagsbits->af$inline rflags))
  :hints (("Goal" :in-theory (enable !rflagsbits->sf$inline rflagsbits->af))))

(defthm flags-af-zf
  (equal (rflagsbits->af$inline (!rflagsbits->zf$inline val rflags))
         (rflagsbits->af$inline rflags))
  :hints (("Goal" :in-theory (enable !rflagsbits->zf$inline rflagsbits->af))))

;;;

(defthm flags-cf-af
  (equal (rflagsbits->cf$inline (!rflagsbits->af$inline val rflags))
         (rflagsbits->cf$inline rflags))
  :hints (("Goal" :in-theory (enable !rflagsbits->af$inline rflagsbits->cf))))

(defthm flags-cf-pf
  (equal (rflagsbits->cf$inline (!rflagsbits->pf$inline val rflags))
         (rflagsbits->cf$inline rflags))
  :hints (("Goal" :in-theory (enable !rflagsbits->pf$inline rflagsbits->cf))))

(defthm flags-cf-of
  (equal (rflagsbits->cf$inline (!rflagsbits->of$inline val rflags))
         (rflagsbits->cf$inline rflags))
  :hints (("Goal" :in-theory (enable !rflagsbits->of$inline rflagsbits->cf))))

(defthm flags-cf-sf
  (equal (rflagsbits->cf$inline (!rflagsbits->sf$inline val rflags))
         (rflagsbits->cf$inline rflags))
  :hints (("Goal" :in-theory (enable !rflagsbits->sf$inline rflagsbits->cf))))

(defthm flags-cf-zf
  (equal (rflagsbits->cf$inline (!rflagsbits->zf$inline val rflags))
         (rflagsbits->cf$inline rflags))
  :hints (("Goal" :in-theory (enable !rflagsbits->zf$inline rflagsbits->cf))))

;;;

(defthm flags-pf-af
  (equal (rflagsbits->pf$inline (!rflagsbits->af$inline val rflags))
         (rflagsbits->pf$inline rflags))
  :hints (("Goal" :in-theory (enable !rflagsbits->af$inline rflagsbits->pf))))

(defthm flags-pf-cf
  (equal (rflagsbits->pf$inline (!rflagsbits->cf$inline val rflags))
         (rflagsbits->pf$inline rflags))
  :hints (("Goal" :in-theory (enable !rflagsbits->cf$inline rflagsbits->pf))))

(defthm flags-pf-of
  (equal (rflagsbits->pf$inline (!rflagsbits->of$inline val rflags))
         (rflagsbits->pf$inline rflags))
  :hints (("Goal" :in-theory (enable !rflagsbits->of$inline rflagsbits->pf))))

(defthm flags-pf-sf
  (equal (rflagsbits->pf$inline (!rflagsbits->sf$inline val rflags))
         (rflagsbits->pf$inline rflags))
  :hints (("Goal" :in-theory (enable !rflagsbits->sf$inline rflagsbits->pf))))

(defthm flags-pf-zf
  (equal (rflagsbits->pf$inline (!rflagsbits->zf$inline val rflags))
         (rflagsbits->pf$inline rflags))
  :hints (("Goal" :in-theory (enable !rflagsbits->zf$inline rflagsbits->pf))))

;;;

(defthm flags-of-af
  (equal (rflagsbits->of$inline (!rflagsbits->af$inline val rflags))
         (rflagsbits->of$inline rflags))
  :hints (("Goal" :in-theory (enable !rflagsbits->af$inline rflagsbits->of))))

(defthm flags-of-cf
  (equal (rflagsbits->of$inline (!rflagsbits->cf$inline val rflags))
         (rflagsbits->of$inline rflags))
  :hints (("Goal" :in-theory (enable !rflagsbits->cf$inline rflagsbits->of))))

(defthm flags-of-pf
  (equal (rflagsbits->of$inline (!rflagsbits->pf$inline val rflags))
         (rflagsbits->of$inline rflags))
  :hints (("Goal" :in-theory (enable !rflagsbits->pf$inline rflagsbits->of))))

(defthm flags-of-sf
  (equal (rflagsbits->of$inline (!rflagsbits->sf$inline val rflags))
         (rflagsbits->of$inline rflags))
  :hints (("Goal" :in-theory (enable !rflagsbits->sf$inline rflagsbits->of))))

(defthm flags-of-zf
  (equal (rflagsbits->of$inline (!rflagsbits->zf$inline val rflags))
         (rflagsbits->of$inline rflags))
  :hints (("Goal" :in-theory (enable !rflagsbits->zf$inline rflagsbits->of))))

;;;

(defthm flags-sf-af
  (equal (rflagsbits->sf$inline (!rflagsbits->af$inline val rflags))
         (rflagsbits->sf$inline rflags))
  :hints (("Goal" :in-theory (enable !rflagsbits->af$inline rflagsbits->sf))))

(defthm flags-sf-cf
  (equal (rflagsbits->sf$inline (!rflagsbits->cf$inline val rflags))
         (rflagsbits->sf$inline rflags))
  :hints (("Goal" :in-theory (enable !rflagsbits->cf$inline rflagsbits->sf))))

(defthm flags-sf-pf
  (equal (rflagsbits->sf$inline (!rflagsbits->pf$inline val rflags))
         (rflagsbits->sf$inline rflags))
  :hints (("Goal" :in-theory (enable !rflagsbits->pf$inline rflagsbits->sf))))

(defthm flags-sf-of
  (equal (rflagsbits->sf$inline (!rflagsbits->of$inline val rflags))
         (rflagsbits->sf$inline rflags))
  :hints (("Goal" :in-theory (enable !rflagsbits->of$inline rflagsbits->sf))))

(defthm flags-sf-zf
  (equal (rflagsbits->sf$inline (!rflagsbits->zf$inline val rflags))
         (rflagsbits->sf$inline rflags))
  :hints (("Goal" :in-theory (enable !rflagsbits->zf$inline rflagsbits->sf))))

;;;

(defthm flags-zf-af
  (equal (rflagsbits->zf$inline (!rflagsbits->af$inline val rflags))
         (rflagsbits->zf$inline rflags))
  :hints (("Goal" :in-theory (enable !rflagsbits->af$inline rflagsbits->zf))))

(defthm flags-zf-cf
  (equal (rflagsbits->zf$inline (!rflagsbits->cf$inline val rflags))
         (rflagsbits->zf$inline rflags))
  :hints (("Goal" :in-theory (enable !rflagsbits->cf$inline rflagsbits->zf))))

(defthm flags-zf-pf
  (equal (rflagsbits->zf$inline (!rflagsbits->pf$inline val rflags))
         (rflagsbits->zf$inline rflags))
  :hints (("Goal" :in-theory (enable !rflagsbits->pf$inline rflagsbits->zf))))

(defthm flags-zf-of
  (equal (rflagsbits->zf$inline (!rflagsbits->of$inline val rflags))
         (rflagsbits->zf$inline rflags))
  :hints (("Goal" :in-theory (enable !rflagsbits->of$inline rflagsbits->zf))))

(defthm flags-zf-sf
  (equal (rflagsbits->zf$inline (!rflagsbits->sf$inline val rflags))
         (rflagsbits->zf$inline rflags))
  :hints (("Goal" :in-theory (enable !rflagsbits->sf$inline rflagsbits->zf))))

;;;

(defthm !rflags-of-xr-rflags-of-set-flag
  (implies (member-equal flag '(:af :cf :pf :of :sf :zf))
           (equal (!rflags (xr :rflags nil (set-flag flag val x86)) x86-2)
                  (set-flag flag val (!rflags (xr :rflags nil  x86) x86-2))))
  :hints (("Goal" :in-theory (enable set-flag
                                     !rflagsbits->af
                                     !rflagsbits->cf
                                     !rflagsbits->pf
                                     !rflagsbits->of
                                     !rflagsbits->sf
                                     !rflagsbits->zf
                                     rflagsbits-fix))))

(defthm xr-rflags-of-!rflags
  (equal (XR :RFLAGS NIL (!RFLAGS rflags x86))
         (bvchop 32 rflags))
  :hints (("Goal" :in-theory (enable !rflags))))

(defthm !rflags-of-xw
  (implies (not (equal fld :rflags))
           (equal (!rflags rflags (xw fld index val x86))
                  (xw fld index val (!rflags rflags x86))))
  :hints (("Goal" :in-theory (enable !rflags))))

(defthm !rflags-of-set-flag
  (equal (!rflags rflags (set-flag flag val x86))
         (!rflags rflags x86))
  :hints (("Goal" :in-theory (enable !rflags set-flag))))

(defthm !rflags-of-!rflags
  (equal (!rflags rflags (!rflags rflags2 x86))
         (!rflags rflags x86))
  :hints (("Goal" :in-theory (enable !rflags))))

(defthm !rflags-does-nothing
  (implies (and (equal (XR :RFLAGS nil X86)
                       (XR :RFLAGS nil X86-2)
                       )
                (x86p x86-2))
           (equal (!RFLAGS (XR :RFLAGS nil X86) X86-2)
                  x86-2))
  :hints (("Goal" :in-theory (enable !rflags))))

(defthm xr-rflags-of-set-flag-af
  (equal (xr :rflags nil (set-flag :af val x86))
         (!rflagsbits->af$inline val (xr :rflags nil x86)))
  :hints (("Goal" :in-theory (enable set-flag))))

(defthm xr-rflags-of-set-flag-cf
  (equal (xr :rflags nil (set-flag :cf val x86))
         (!rflagsbits->cf$inline val (xr :rflags nil x86)))
  :hints (("Goal" :in-theory (enable set-flag))))

(defthm xr-rflags-of-set-flag-pf
  (equal (xr :rflags nil (set-flag :pf val x86))
         (!rflagsbits->pf$inline val (xr :rflags nil x86)))
  :hints (("Goal" :in-theory (enable set-flag))))

(defthm xr-rflags-of-set-flag-of
  (equal (xr :rflags nil (set-flag :of val x86))
         (!rflagsbits->of$inline val (xr :rflags nil x86)))
  :hints (("Goal" :in-theory (enable set-flag))))

(defthm xr-rflags-of-set-flag-sf
  (equal (xr :rflags nil (set-flag :sf val x86))
         (!rflagsbits->sf$inline val (xr :rflags nil x86)))
  :hints (("Goal" :in-theory (enable set-flag))))

(defthm xr-rflags-of-set-flag-zf
  (equal (xr :rflags nil (set-flag :zf val x86))
         (!rflagsbits->zf$inline val (xr :rflags nil x86)))
  :hints (("Goal" :in-theory (enable set-flag))))

;todo: are there more flags to clear.
;to be left enabled, for now
;only used in one example
(defun clear-all-flags (x86)
  (declare (xargs :stobjs x86))
  (let* ((x86 (set-flag :af 0 x86))
         (x86 (set-flag :cf 0 x86))
         (x86 (set-flag :of 0 x86))
         (x86 (set-flag :pf 0 x86))
         (x86 (set-flag :sf 0 x86))
         (x86 (set-flag :zf 0 x86)))
    x86))

(defthm set-flag-of-if
  (equal (set-flag flag val (if test x y))
         (if test
             (set-flag flag val x)
           (set-flag flag val y))))

(defthm set-flag-of-get-flag-same
  (implies (member-equal flag *flags*)
           (equal (set-flag flag (get-flag flag x86) x86)
                  x86))
  :hints (("Goal" :in-theory (enable get-flag set-flag
                                     !rflagsbits->af rflagsbits->af
                                     !rflagsbits->cf rflagsbits->cf
                                     !rflagsbits->of rflagsbits->of
                                     !rflagsbits->pf rflagsbits->pf
                                     !rflagsbits->sf rflagsbits->sf
                                     !rflagsbits->zf rflagsbits->zf
                                     !rflagsbits->id rflagsbits->id
                                     !rflagsbits->tf rflagsbits->tf
                                     !rflagsbits->nt rflagsbits->nt
                                     !rflagsbits->df rflagsbits->df
                                     !rflagsbits->vm rflagsbits->vm
                                     !rflagsbits->ac rflagsbits->ac
                                     !rflagsbits->rf rflagsbits->rf
                                     !rflagsbits->vif rflagsbits->vif
                                     !rflagsbits->vip rflagsbits->vip
                                     !rflagsbits->iopl rflagsbits->iopl
                                     !rflagsbits->intf rflagsbits->intf))))

;; This allows the state terms to differ
(defthm set-flag-of-get-flag-same-gen
  (implies (and (equal (get-flag flag x86_2)
                       (get-flag flag x86))
                (member-equal flag *flags*))
           (equal (set-flag flag (get-flag flag x86_2) x86)
                  x86)))

(defthm if-of-set-flag-and-set-flag
  (equal (if test (set-flag flag val1 x86) (set-flag flag val2 x86))
         (set-flag flag (if test val1 val2) x86)))

(defthm get-flag-of-!rflags-of-xr
  (equal (get-flag flag (!rflags (xr ':rflags 'nil x86_1) x86_2))
         (get-flag flag x86_1))
  :hints (("Goal" :in-theory (enable !rflags get-flag))))

(defthm get-flag-of-xw-rflags-of-xr-rflags
  (equal (get-flag flag (xw :rflags nil (xr ':rflags 'nil x86_1) x86_2))
         (get-flag flag x86_1))
  :hints (("Goal" :in-theory (enable !rflags get-flag))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm rflagsbits->af-of-bvif
  (implies (and (<= 5 size)
                (integerp size))
           (equal (rflagsbits->af (bvif size test tp ep))
                  (if test (rflagsbits->af tp) (rflagsbits->af ep))))
  :hints (("Goal" :in-theory (enable rflagsbits->af rflagsbits-fix))))

(defthm rflagsbits->cf-of-bvif
  (implies (and (<= 1 size)
                (integerp size))
           (equal (rflagsbits->cf (bvif size test tp ep))
                  (if test (rflagsbits->cf tp) (rflagsbits->cf ep))))
  :hints (("Goal" :in-theory (enable rflagsbits->cf rflagsbits-fix))))

(defthm rflagsbits->of-of-bvif
  (implies (and (<= 12 size)
                (integerp size))
           (equal (rflagsbits->of (bvif size test tp ep))
                  (if test (rflagsbits->of tp) (rflagsbits->of ep))))
  :hints (("Goal" :in-theory (enable rflagsbits->of rflagsbits-fix))))

(defthm rflagsbits->pf-of-bvif
  (implies (and (<= 3 size)
                (integerp size))
           (equal (rflagsbits->pf (bvif size test tp ep))
                  (if test (rflagsbits->pf tp) (rflagsbits->pf ep))))
  :hints (("Goal" :in-theory (enable rflagsbits->pf rflagsbits-fix))))

(defthm rflagsbits->sf-of-bvif
  (implies (and (<= 8 size)
                (integerp size))
           (equal (rflagsbits->sf (bvif size test tp ep))
                  (if test (rflagsbits->sf tp) (rflagsbits->sf ep))))
  :hints (("Goal" :in-theory (enable rflagsbits->sf rflagsbits-fix))))

(defthm rflagsbits->zf-of-bvif
  (implies (and (<= 7 size)
                (integerp size))
           (equal (rflagsbits->zf (bvif size test tp ep))
                  (if test (rflagsbits->zf tp) (rflagsbits->zf ep))))
  :hints (("Goal" :in-theory (enable rflagsbits->zf rflagsbits-fix))))

(defthmd !rflags-becomes-xw
  (equal (!rflags rflags x86)
         (xw :rflags nil rflags x86)))

(defthmd rflags-becomes-xr
  (equal (rflags x86)
         (xr :rflags nil x86)))

;needed?
(defthm xr-of-rflags-and-xw-of-rflags
  (equal (xr :rflags nil (xw :rflags nil rflags x86))
         (bvchop 32 rflags)))

(defthm xw-of-rflags-and-set-flag
  (equal (xw :rflags nil rflags (set-flag flag val x86))
         (xw :rflags nil rflags x86))
  :hints (("Goal" :in-theory (enable set-flag))))

;gen?
(defthm xw-of-rflags-does-nothing
  (implies (equal rflags (xr :rflags nil x86))
           (equal (xw :rflags nil rflags x86)
                  x86)))

(defthm xw-of-rflags-of-xw
  (implies (not (equal fld :rflags))
           (equal (xw :rflags nil rflags (xw fld index val x86))
                  (xw fld index val (xw :rflags nil rflags x86))))
  :hints (("Goal" :in-theory (enable set-flag))))

(defthm xw-rflags-of-set-flag
  (equal (xw :rflags nil rflags (set-flag flag val x86))
         (xw :rflags nil rflags x86))
  :hints (("Goal" :in-theory (enable !rflags set-flag))))

(defthm memi-of-set-flag
  (equal (memi addr (set-flag flag val x86))
         (memi addr x86))
  :hints (("Goal" :in-theory (enable memi set-flag))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; todo: more like this
;; or should we use a "convert-to-bv" function?
;; todo: install these in a rule-list
(defthm trim-of-!rflagsbits->cf
  (implies (and (unsigned-byte-p 1 cf)
                (<= 1 size)
                (<= size 32)
                (integerp size))
           (equal (trim size (!rflagsbits->cf cf rflags))
                  (bvcat (+ -1 size) (slice 31 1 rflags)
                         1 cf)))
  :hints (("Goal" :in-theory (enable !rflagsbits->cf bfix rflagsbits-fix))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; todo: more like this
(defthm getbit-of-!rflagsbits->af
  (implies (and (unsigned-byte-p 1 af)
                (natp n)
                (< n 32))
           (equal (getbit n (!rflagsbits->af af rflags))
                  (if (equal n 4)
                      af
                    (getbit n rflags))))
  :hints (("Goal" :in-theory (enable !rflagsbits->af bfix rflagsbits-fix))))

(defthm getbit-of-!rflagsbits->cf
  (implies (and (unsigned-byte-p 1 cf)
                (natp n)
                (< n 32))
           (equal (getbit n (!rflagsbits->cf cf rflags))
                  (if (equal n 0)
                      cf
                    (getbit n rflags))))
  :hints (("Goal" :in-theory (enable !rflagsbits->cf bfix rflagsbits-fix))))

(defthm getbit-of-!rflagsbits->of
  (implies (and (unsigned-byte-p 1 of)
                (natp n)
                (< n 32))
           (equal (getbit n (!rflagsbits->of of rflags))
                  (if (equal n 11)
                      of
                    (getbit n rflags))))
  :hints (("Goal" :in-theory (enable !rflagsbits->of bfix rflagsbits-fix))))

(defthm getbit-of-!rflagsbits->pf
  (implies (and (unsigned-byte-p 1 pf)
                (natp n)
                (< n 32))
           (equal (getbit n (!rflagsbits->pf pf rflags))
                  (if (equal n 2)
                      pf
                    (getbit n rflags))))
  :hints (("Goal" :in-theory (enable !rflagsbits->pf bfix rflagsbits-fix))))

(defthm getbit-of-!rflagsbits->sf
  (implies (and (unsigned-byte-p 1 sf)
                (natp n)
                (< n 32))
           (equal (getbit n (!rflagsbits->sf sf rflags))
                  (if (equal n 7)
                      sf
                    (getbit n rflags))))
  :hints (("Goal" :in-theory (enable !rflagsbits->sf bfix rflagsbits-fix))))

(defthm getbit-of-!rflagsbits->zf
  (implies (and (unsigned-byte-p 1 zf)
                (natp n)
                (< n 32))
           (equal (getbit n (!rflagsbits->zf zf rflags))
                  (if (equal n 6)
                      zf
                    (getbit n rflags))))
  :hints (("Goal" :in-theory (enable !rflagsbits->zf bfix rflagsbits-fix))))
