; Support for using Axe to reason about x86 code
;
; Copyright (C) 2016-2019 Kestrel Technology, LLC
; Copyright (C) 2020-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; This book contains supporting material that is Axe-specific (e.g., rules
;; that use axe-syntaxp or axe-bind-free).

;; TODO: Factor out any non-Axe-specific stuff

;; TODO: Make sure there are non-axe versions of all of these.

(include-book "kestrel/x86/assumptions64" :dir :system) ;for ADDRESSES-OF-SUBSEQUENT-STACK-SLOTS-AUX
(include-book "kestrel/x86/assumptions32" :dir :system) ; for return-address-okp
(include-book "kestrel/x86/conditions" :dir :system) ; for jnl-condition
(include-book "kestrel/x86/write-over-write-rules64" :dir :system)
(include-book "kestrel/x86/run-until-return" :dir :system)
(include-book "kestrel/x86/run-until-return2" :dir :system) ; new scheme
(include-book "kestrel/x86/run-until-return3" :dir :system) ; newer scheme
(include-book "kestrel/x86/run-until-return4" :dir :system) ; newer scheme, 32-bit
(include-book "kestrel/x86/floats" :dir :system)
(include-book "kestrel/memory/memory48" :dir :system)
(include-book "kestrel/x86/canonical-unsigned" :dir :system)
(include-book "../axe-syntax")
(include-book "../known-booleans")
(include-book "../axe-syntax-functions-bv") ; for term-should-be-trimmed-axe
(include-book "../axe-syntax-functions")
(include-book "axe-syntax-functions-x86")
(include-book "kestrel/bv-lists/bv-array-read-chunk-little" :dir :system)
(local (include-book "kestrel/utilities/mv-nth" :dir :system))

;; Register a bunch of x86-related functions as known booleans:

;; mostly to suppress messages (but does this slow down anything?):
;; todo: have this print :redundant when it is
(add-known-boolean canonical-address-p$inline)
(add-known-boolean unsigned-canonical-address-p)
(add-known-boolean canonical-address-listp)
(add-known-boolean disjoint-p)
(add-known-boolean program-at)
(add-known-boolean x86p)
(add-known-boolean 64-bit-modep)
(add-known-boolean app-view)
;(add-known-boolean addr-byte-alistp)
(add-known-boolean subset-p)
(add-known-boolean no-duplicates-p)
(add-known-boolean member-p)
(add-known-boolean separate)
(add-known-boolean alignment-checking-enabled-p)

;; I'm not sure if these are necessary:
(add-known-boolean jnl-condition) ;todo: more

;; 32-bit stuff:
(add-known-boolean segment-is-32-bitsp)
(add-known-boolean well-formed-32-bit-segmentp)
(add-known-boolean code-segment-well-formedp)
(add-known-boolean code-segment-assumptions32-for-code)
(add-known-boolean eff-addrs-okp)
(add-known-boolean eff-addr-okp)
(add-known-boolean segments-separate)

(add-known-boolean return-address-okp)

(add-known-boolean cr0bits-p$inline)
(add-known-boolean cr3bits-p$inline)
(add-known-boolean cr4bits-p$inline)
(add-known-boolean cr8bits-p$inline)

(add-known-boolean is-nan)
(add-known-boolean infp)
(add-known-boolean nanp)

(add-known-boolean in-region48p)
(add-known-boolean subregion48p)
(add-known-boolean disjoint-regions48p)

(add-known-boolean in-region64p)
(add-known-boolean subregion64p)
(add-known-boolean disjoint-regions64p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;todo: move
;; (defthm not-member-p-canonical-address-listp-when-disjoint-p-alt
;;   (implies (and (disjoint-p (create-canonical-address-list m addr) ;this hyp is commuted
;;                             (create-canonical-address-list n prog-addr))
;;                 (member-p e (create-canonical-address-list m addr)))
;;            (not (member-p e (create-canonical-address-list n prog-addr)))))

;We'll use aref1-rewrite to handle the aref1s.
;; Or can we evaluate the aref1s (without getting slow array warnings)?
(defthmd aref1-rewrite ;for axe
  (implies (and (not (equal :header n))
                (not (equal :default n))
                (assoc-equal n l))
           (equal (aref1 name l n)
                  (lookup-equal n l)))
  :hints (("Goal" :in-theory (enable lookup-equal aref1))))

(defopeners 64-bit-mode-two-byte-opcode-modr/m-p
                  :hyps ((syntaxp (quotep x86isa::opcode))
                         (unsigned-byte-p 8 x86isa::opcode)))

;why did this cause loops?
;move
(defthm canonical-address-listp-of-cdr
  (implies (canonical-address-listp lst)
           (canonical-address-listp (cdr lst))))

;;(defopeners COMBINE-BYTES :hyps ((syntaxp (quotep x86isa::bytes))))

;;  Use def-constant-opener to enable Axe to evaluate ground calls of various
;;  functions:

(def-constant-opener logcount)
(def-constant-opener logapp)
(def-constant-opener lognot)

(def-constant-opener zip)
(def-constant-opener separate)
(def-constant-opener nonnegative-integer-quotient)
(def-constant-opener evenp)

(def-constant-opener bool->bit$inline)
(def-constant-opener acl2::rotate-left)
(def-constant-opener acl2::rotate-right)

;; Flag-related functions (these seem safe to execute without that requiring
;; more rules; for example, we expect jle-condition to always be called on flag
;; functions with the same arguments (dst and src), so either all the args to
;; jle-condition get evaluated or none of them do).

(def-constant-opener zf-spec$inline)

(def-constant-opener cf-spec8$inline)
(def-constant-opener of-spec8$inline)
(def-constant-opener pf-spec8$inline)
(def-constant-opener sf-spec8$inline)
(def-constant-opener adc-af-spec8$inline)
(def-constant-opener add-af-spec8$inline)
(def-constant-opener sub-af-spec8$inline)
(def-constant-opener sub-cf-spec8) ; todo: make these inline, like the others
(def-constant-opener sub-of-spec8)
(def-constant-opener sub-pf-spec8)
(def-constant-opener sub-sf-spec8)
(def-constant-opener sub-zf-spec8)

(def-constant-opener cf-spec16$inline)
(def-constant-opener of-spec16$inline)
(def-constant-opener pf-spec16$inline)
(def-constant-opener sf-spec16$inline)
(def-constant-opener adc-af-spec16$inline)
(def-constant-opener add-af-spec16$inline)
(def-constant-opener sub-af-spec16$inline)
(def-constant-opener sub-cf-spec16)
(def-constant-opener sub-of-spec16)
(def-constant-opener sub-pf-spec16)
(def-constant-opener sub-sf-spec16)
(def-constant-opener sub-zf-spec16)

(def-constant-opener cf-spec32$inline)
(def-constant-opener of-spec32$inline)
(def-constant-opener pf-spec32$inline)
(def-constant-opener sf-spec32$inline)
(def-constant-opener adc-af-spec32$inline)
(def-constant-opener add-af-spec32$inline)
(def-constant-opener sub-af-spec32$inline)
(def-constant-opener sub-cf-spec32)
(def-constant-opener sub-of-spec32)
(def-constant-opener sub-pf-spec32)
(def-constant-opener sub-sf-spec32)
(def-constant-opener sub-zf-spec32)

(def-constant-opener cf-spec64$inline)
(def-constant-opener of-spec64$inline)
(def-constant-opener pf-spec64$inline)
(def-constant-opener sf-spec64$inline)
(def-constant-opener adc-af-spec64$inline)
(def-constant-opener add-af-spec64$inline)
(def-constant-opener sub-af-spec64$inline)
(def-constant-opener sub-cf-spec64)
(def-constant-opener sub-of-spec64)
(def-constant-opener sub-pf-spec64)
(def-constant-opener sub-sf-spec64)
(def-constant-opener sub-zf-spec64)

(def-constant-opener !rflagsbits->ac$inline)
(def-constant-opener !rflagsbits->af$inline)
(def-constant-opener !rflagsbits->cf$inline)
(def-constant-opener !rflagsbits->of$inline)
(def-constant-opener !rflagsbits->pf$inline)
(def-constant-opener !rflagsbits->sf$inline)
(def-constant-opener !rflagsbits->zf$inline)

(def-constant-opener one-byte-opcode-modr/m-p$inline)
(def-constant-opener two-byte-opcode-modr/m-p$inline)

(def-constant-opener rflagsbits->ac$inline)
(def-constant-opener rflagsbits->af$inline)
(def-constant-opener rflagsbits->cf$inline)
(def-constant-opener rflagsbits->of$inline)
(def-constant-opener rflagsbits->pf$inline)
(def-constant-opener rflagsbits->sf$inline)
(def-constant-opener rflagsbits->zf$inline)
(def-constant-opener rflagsbits->res1$inline)
(def-constant-opener rflagsbits->res2$inline)
(def-constant-opener rflagsbits->res3$inline)
(def-constant-opener rflagsbits->tf$inline)
(def-constant-opener rflagsbits->intf$inline)
(def-constant-opener rflagsbits->df$inline)
(def-constant-opener rflagsbits->iopl$inline)
(def-constant-opener rflagsbits->nt$inline)
(def-constant-opener rflagsbits->res4$inline)
(def-constant-opener rflagsbits->rf$inline)
(def-constant-opener rflagsbits->vm$inline)
(def-constant-opener rflagsbits->vif$inline)
(def-constant-opener rflagsbits->vip$inline)
(def-constant-opener rflagsbits->id$inline)
(def-constant-opener rflagsbits->res5$inline)

(def-constant-opener rflagsbits$inline)
(def-constant-opener rflagsbits-fix$inline)

;; For now, I'm trying just always opening these:
;; See books/projects/x86isa/utils/basic-structs.lisp
;; (def-constant-opener x86isa::2bits-fix)
;; (def-constant-opener x86isa::3bits-fix)
;; (def-constant-opener x86isa::4bits-fix)
;; (def-constant-opener x86isa::5bits-fix)
;; (def-constant-opener x86isa::6bits-fix)
;; (def-constant-opener x86isa::7bits-fix)
;; (def-constant-opener x86isa::8bits-fix)
;; (def-constant-opener x86isa::10bits-fix)
;; (def-constant-opener x86isa::11bits-fix)
;; (def-constant-opener x86isa::12bits-fix)
;; (def-constant-opener x86isa::13bits-fix)
;; (def-constant-opener x86isa::16bits-fix)
;; (def-constant-opener x86isa::17bits-fix)
;; (def-constant-opener x86isa::19bits-fix)
;; (def-constant-opener x86isa::22bits-fix)
;; (def-constant-opener x86isa::24bits-fix)
;; (def-constant-opener x86isa::31bits-fix)
;; (def-constant-opener x86isa::32bits-fix)
;; (def-constant-opener x86isa::36bits-fix)
;; (def-constant-opener x86isa::40bits-fix)
;; (def-constant-opener x86isa::45bits-fix)
;; (def-constant-opener x86isa::54bits-fix)
;; (def-constant-opener x86isa::64bits-fix)

(def-constant-opener expt2$inline)

(def-constant-opener feature-flags); needed?

(def-constant-opener 32-bit-mode-two-byte-opcode-modr/m-p)
(def-constant-opener 32-bit-compute-mandatory-prefix-for-two-byte-opcode$inline)

;; TODO: Think about whether to use regular rules, constant opener rules, or build into the evaluator.

;; Functions introduced by defbitstruct:

(def-constant-opener prefixes-fix$inline)
(def-constant-opener prefixes->num$inline)
(def-constant-opener prefixes->lck$inline)
(def-constant-opener prefixes->rep$inline)
(def-constant-opener prefixes->seg$inline)
(def-constant-opener prefixes->opr$inline)
(def-constant-opener prefixes->adr$inline)
(def-constant-opener prefixes->nxt$inline)
(def-constant-opener !prefixes->num$inline)
(def-constant-opener !prefixes->lck$inline)
(def-constant-opener !prefixes->rep$inline)
(def-constant-opener !prefixes->seg$inline)
(def-constant-opener !prefixes->opr$inline)
(def-constant-opener !prefixes->adr$inline)
(def-constant-opener !prefixes->nxt$inline)

(def-constant-opener vex-prefixes-fix$inline)
(def-constant-opener vex-prefixes->byte0$inline)
(def-constant-opener vex-prefixes->byte1$inline)
(def-constant-opener vex-prefixes->byte2$inline)
(def-constant-opener !vex-prefixes->byte0$inline)
(def-constant-opener !vex-prefixes->byte1$inline)
(def-constant-opener !vex-prefixes->byte2$inline)

(def-constant-opener vex2-byte1-fix$inline)
(def-constant-opener vex2-byte1->pp$inline)
(def-constant-opener vex2-byte1->l$inline)
(def-constant-opener vex2-byte1->vvvv$inline)
(def-constant-opener vex2-byte1->r$inline)

;; can we optimize these by avoiding introducing the fix?
(def-constant-opener vex3-byte1-fix$inline)
(def-constant-opener vex3-byte1->m-mmmm$inline)
(def-constant-opener vex3-byte1->b$inline)
(def-constant-opener vex3-byte1->x$inline)
(def-constant-opener vex3-byte1->r$inline)

(def-constant-opener vex3-byte2-fix$inline)
(def-constant-opener vex3-byte2->pp$inline)
(def-constant-opener vex3-byte2->l$inline)
(def-constant-opener vex3-byte2->vvvv$inline)
(def-constant-opener vex3-byte2->w$inline)

(def-constant-opener evex-prefixes-fix$inline)
(def-constant-opener evex-prefixes->byte0$inline)
(def-constant-opener evex-prefixes->byte1$inline)
(def-constant-opener evex-prefixes->byte2$inline)
(def-constant-opener evex-prefixes->byte3$inline)
(def-constant-opener !evex-prefixes->byte0$inline)
(def-constant-opener !evex-prefixes->byte1$inline)
(def-constant-opener !evex-prefixes->byte2$inline)
(def-constant-opener !evex-prefixes->byte3$inline)

(def-constant-opener evex-byte1-fix$inline)
(def-constant-opener evex-byte1->mmm$inline)
(def-constant-opener evex-byte1->res$inline)
(def-constant-opener evex-byte1->r-prime$inline)
(def-constant-opener evex-byte1->b$inline)
(def-constant-opener evex-byte1->x$inline)
(def-constant-opener evex-byte1->r$inline)

(def-constant-opener evex-byte2-fix$inline)
(def-constant-opener evex-byte2->pp$inline)
(def-constant-opener evex-byte2->res$inline)
(def-constant-opener evex-byte2->vvvv$inline)
(def-constant-opener evex-byte2->w$inline)

(def-constant-opener evex-byte3-fix$inline)
(def-constant-opener evex-byte3->aaa$inline)
(def-constant-opener evex-byte3->v-prime$inline)
(def-constant-opener evex-byte3->b$inline)
(def-constant-opener evex-byte3->vl/rc$inline)
(def-constant-opener evex-byte3->z$inline)

(def-constant-opener modr/m-fix$inline)
(def-constant-opener modr/m->r/m$inline)
(def-constant-opener modr/m->reg$inline)
(def-constant-opener modr/m->mod$inline)

(def-constant-opener x86isa::sib-fix$inline)
(def-constant-opener x86isa::sib->base$inline)
(def-constant-opener x86isa::sib->index$inline)
(def-constant-opener x86isa::sib->scale$inline)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-constant-opener x86isa::vex-opcode-modr/m-p$inline)
(def-constant-opener x86isa::vex-prefixes-map-p$inline)

(def-constant-opener vex->vvvv$inline)
(def-constant-opener vex->l$inline)
(def-constant-opener vex->pp$inline)
(def-constant-opener vex->r$inline)
(def-constant-opener vex->w$inline)
(def-constant-opener vex->b$inline)
(def-constant-opener vex->x$inline)


(def-constant-opener x86isa::rex-byte-from-vex-prefixes)

(def-constant-opener x86isa::vex-vvvv-reg-index)

(def-constant-opener canonical-address-p$inline)

;(defopeners byte-ify :hyps ((syntaxp (and (quotep n) (quotep val)))))

(def-constant-opener byte-listp)

(def-constant-opener mxcsrbits-fix)

;; these expose part-select
(def-constant-opener mxcsrbits->ie$inline)
(def-constant-opener mxcsrbits->de$inline)
(def-constant-opener mxcsrbits->ze$inline)
(def-constant-opener mxcsrbits->oe$inline)
(def-constant-opener mxcsrbits->ue$inline)
(def-constant-opener mxcsrbits->pe$inline)
(def-constant-opener mxcsrbits->daz$inline)
(def-constant-opener mxcsrbits->im$inline)
(def-constant-opener mxcsrbits->dm$inline)
(def-constant-opener mxcsrbits->zm$inline)
(def-constant-opener mxcsrbits->om$inline)
(def-constant-opener mxcsrbits->um$inline)
(def-constant-opener mxcsrbits->pm$inline)
(def-constant-opener mxcsrbits->rc$inline)
(def-constant-opener mxcsrbits->ftz$inline)
(def-constant-opener mxcsrbits->reserved$inline)

(def-constant-opener convert-arith-operation-to-rtl-op$inline)
;(def-constant-opener feature-flag) ; keep feature-flag disabled, for clarity
;(def-constant-opener x86isa::cpuid-flag-fn) ; can't do this, it's an encapsulate
(def-constant-opener rtl::set-flag) ; drop?

(def-constant-opener in-region48p)
(def-constant-opener subregion48p)
(def-constant-opener disjoint-regions48p)

(def-constant-opener in-region64p)
(def-constant-opener subregion64p)
(def-constant-opener disjoint-regions64p)
(def-constant-opener unsigned-canonical-address-p)

(acl2::def-constant-opener seg-regp)
(acl2::def-constant-opener integer-range-p)

(defopeners acl2::get-symbol-table-entry-mach-o)
(defopeners acl2::get-all-sections-from-mach-o-load-commands)
(defopeners acl2::get-section-number-mach-o-aux)

(defopeners addresses-of-subsequent-stack-slots-aux)

(defopeners acl2::get-pe-section-info-aux)
(defopeners acl2::lookup-pe-symbol)

(defopeners simd-add-spec)
(defopeners simd-sub-spec)

;; ;todo
;; (thm
;;  (equal (bitops::rotate-left-32 x places)
;;         (acl2::leftrotate32 places x))
;;  :hints (("Goal" :in-theory (enable bitops::rotate-left-32 ACL2::ROTATE-LEFT acl2::leftrotate32 acl2::leftrotate))))

;; For use by Axe.  Can't disable since this is in :rule-classes nil.
(defthm set-flag-of-set-flag-diff-axe
  (implies (and (syntaxp (and (quotep flag1)
                              (quotep flag2)
                              ))
                (axe-syntaxp (lighter-dargp flag2 flag1))
                (not (equal flag1 flag2))
                (member-eq flag1 *flags*)
                (member-eq flag2 *flags*)
                )
           (equal (set-flag flag1 val1 (set-flag flag2 val2 x86))
                  (set-flag flag2 val2 (set-flag flag1 val1 x86))))
  :hints (("Goal" :use (:instance set-flag-of-set-flag-diff)
           :in-theory (disable set-flag-of-set-flag-diff)))
  :rule-classes nil)

;; For use by Axe.
;; todo: package
(defthmd x86isa::idiv-spec-64-trim-arg1-axe-all
  (implies (axe-syntaxp (term-should-be-trimmed-axe '128 x 'acl2::all dag-array))
           (equal (idiv-spec-64 x y)
                  (idiv-spec-64 (trim 128 x) y)))
  :hints (("Goal" :in-theory (enable trim idiv-spec-64))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; For use by Axe.
;; Only fires when x86 is not an IF/MYIF (to save time).
(defthmd run-until-stack-shorter-than-base-axe
  (implies (and (axe-syntaxp (not (syntactic-call-of 'if x86 dag-array)))
                ;; (axe-syntaxp (not (syntactic-call-of 'myif x86 dag-array))) ; may be needed someday
                (stack-shorter-thanp old-rsp x86))
           (equal (run-until-stack-shorter-than old-rsp x86)
                  x86))
  :hints (("Goal" :in-theory (enable run-until-stack-shorter-than-base))))

;; For use by Axe.
;; Only fires when x86 is not an IF/MYIF (so we don't need IF lifting rules for x86-fetch-decode-execute and its subfunctions).
(defthmd run-until-stack-shorter-than-opener-axe
  (implies (and (axe-syntaxp (not (syntactic-call-of 'if x86 dag-array)))
                ;; (axe-syntaxp (not (syntactic-call-of 'myif x86 dag-array))) ; may be needed someday
                (not (stack-shorter-thanp old-rsp x86)))
           (equal (run-until-stack-shorter-than old-rsp x86)
                  (run-until-stack-shorter-than old-rsp (x86-fetch-decode-execute x86))))
  :hints (("Goal" :in-theory (enable run-until-stack-shorter-than-opener))))

;; For use by Axe.
;; Only fires when x86 is not an IF/MYIF (to save time).
(defthmd run-until-stack-shorter-than-or-reach-pc-base-axe
  (implies (and (axe-syntaxp (not (syntactic-call-of 'if x86 dag-array)))
                ;; (axe-syntaxp (not (syntactic-call-of 'myif x86 dag-array))) ; may be needed someday
                (or (stack-shorter-thanp old-rsp x86)
                    (member-equal (rip x86) stop-pcs)))
           (equal (run-until-stack-shorter-than-or-reach-pc old-rsp stop-pcs x86)
                  x86))
  :hints (("Goal" :in-theory (enable run-until-stack-shorter-than-or-reach-pc-base))))

;; For use by Axe.
;; Only fires when x86 is not an IF/MYIF (so we don't need IF lifting rules for x86-fetch-decode-execute and its subfunctions).
(defthmd run-until-stack-shorter-than-or-reach-pc-opener-axe
  (implies (and (axe-syntaxp (not (syntactic-call-of 'if x86 dag-array)))
                ;; (axe-syntaxp (not (syntactic-call-of 'myif x86 dag-array))) ; may be needed someday
                (not (stack-shorter-thanp old-rsp x86))
                (not (member-equal (rip x86) stop-pcs)))
           (equal (run-until-stack-shorter-than-or-reach-pc old-rsp stop-pcs x86)
                  (run-until-stack-shorter-than-or-reach-pc old-rsp stop-pcs (x86-fetch-decode-execute x86))))
  :hints (("Goal" :in-theory (enable run-until-stack-shorter-than-or-reach-pc-opener))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; new scheme:

;; For use by Axe.
;; Only fires when x86 is not an IF/MYIF (to save time).
(defthmd run-until-rsp-is-base-axe
  (implies (and (axe-syntaxp (not (syntactic-call-of 'if x86 dag-array)))
                ;; (axe-syntaxp (not (syntactic-call-of 'myif x86 dag-array))) ; may be needed someday
                (equal rsp (xr :rgf *rsp* x86)))
           (equal (run-until-rsp-is rsp x86)
                  x86))
  :hints (("Goal" :in-theory (enable run-until-rsp-is-base))))

;; For use by Axe.
;; Only fires when x86 is not an IF/MYIF (so we don't need IF lifting rules for x86-fetch-decode-execute and its subfunctions).
(defthmd run-until-rsp-is-opener-axe
  (implies (and (axe-syntaxp (not (syntactic-call-of 'if x86 dag-array)))
                ;; (axe-syntaxp (not (syntactic-call-of 'myif x86 dag-array))) ; may be needed someday
                (not (equal rsp (xr :rgf *rsp* x86))))
           (equal (run-until-rsp-is rsp x86)
                  (run-until-rsp-is rsp (x86-fetch-decode-execute x86))))
  :hints (("Goal" :in-theory (enable run-until-rsp-is-opener))))

;; For use by Axe.
;; Only fires when x86 is not an IF/MYIF (to save time).
(defthmd run-until-rsp-is-or-reach-pc-base-axe
  (implies (and (axe-syntaxp (not (syntactic-call-of 'if x86 dag-array)))
                ;; (axe-syntaxp (not (syntactic-call-of 'myif x86 dag-array))) ; may be needed someday
                (or (equal rsp (xr :rgf *rsp* x86))
                    (member-equal (rip x86) stop-pcs)))
           (equal (run-until-rsp-is-or-reach-pc rsp stop-pcs x86)
                  x86))
  :hints (("Goal" :in-theory (enable run-until-rsp-is-or-reach-pc-base))))

;; For use by Axe.
;; Only fires when x86 is not an IF/MYIF (so we don't need IF lifting rules for x86-fetch-decode-execute and its subfunctions).
(defthmd run-until-rsp-is-or-reach-pc-opener-axe
  (implies (and (axe-syntaxp (not (syntactic-call-of 'if x86 dag-array)))
                ;; (axe-syntaxp (not (syntactic-call-of 'myif x86 dag-array))) ; may be needed someday
                (not (equal rsp (xr :rgf *rsp* x86)))
                (not (member-equal (rip x86) stop-pcs)))
           (equal (run-until-rsp-is-or-reach-pc rsp stop-pcs x86)
                  (run-until-rsp-is-or-reach-pc rsp stop-pcs (x86-fetch-decode-execute x86))))
  :hints (("Goal" :in-theory (enable run-until-rsp-is-or-reach-pc-opener))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; newer scheme:

;; For use by Axe.
;; Only fires when x86 is not an IF/MYIF (to save time).
(defthmd run-until-rsp-is-above-base-axe
  (implies (and (axe-syntaxp (not (syntactic-call-of 'if x86 dag-array)))
                ;; (axe-syntaxp (not (syntactic-call-of 'myif x86 dag-array))) ; may be needed someday
                (rsp-is-abovep old-rsp x86))
           (equal (run-until-rsp-is-above old-rsp x86)
                  x86))
  :hints (("Goal" :in-theory (enable run-until-rsp-is-above-base))))

;; For use by Axe.
;; Only fires when x86 is not an IF/MYIF (so we don't need IF lifting rules for x86-fetch-decode-execute and its subfunctions).
(defthmd run-until-rsp-is-above-opener-axe
  (implies (and (axe-syntaxp (not (syntactic-call-of 'if x86 dag-array)))
                ;; (axe-syntaxp (not (syntactic-call-of 'myif x86 dag-array))) ; may be needed someday
                (not (rsp-is-abovep old-rsp x86)))
           (equal (run-until-rsp-is-above old-rsp x86)
                  (run-until-rsp-is-above old-rsp (x86-fetch-decode-execute x86))))
  :hints (("Goal" :in-theory (enable run-until-rsp-is-above-opener))))

;; For use by Axe.
;; Only fires when x86 is not an IF/MYIF (to save time).
(defthmd run-until-rsp-is-above-or-reach-pc-base-axe
  (implies (and (axe-syntaxp (not (syntactic-call-of 'if x86 dag-array)))
                ;; (axe-syntaxp (not (syntactic-call-of 'myif x86 dag-array))) ; may be needed someday
                (or (rsp-is-abovep old-rsp x86)
                    (member-equal (rip x86) stop-pcs)))
           (equal (run-until-rsp-is-above-or-reach-pc old-rsp stop-pcs x86)
                  x86))
  :hints (("Goal" :in-theory (enable run-until-rsp-is-above-or-reach-pc-base))))

;; For use by Axe.
;; Only fires when x86 is not an IF/MYIF (so we don't need IF lifting rules for x86-fetch-decode-execute and its subfunctions).
(defthmd run-until-rsp-is-above-or-reach-pc-opener-axe
  (implies (and (axe-syntaxp (not (syntactic-call-of 'if x86 dag-array)))
                ;; (axe-syntaxp (not (syntactic-call-of 'myif x86 dag-array))) ; may be needed someday
                (not (rsp-is-abovep old-rsp x86))
                (not (member-equal (rip x86) stop-pcs)))
           (equal (run-until-rsp-is-above-or-reach-pc old-rsp stop-pcs x86)
                  (run-until-rsp-is-above-or-reach-pc old-rsp stop-pcs (x86-fetch-decode-execute x86))))
  :hints (("Goal" :in-theory (enable run-until-rsp-is-above-or-reach-pc-opener))))

;; newer scheme, 32-bit:

;; For use by Axe.
;; Only fires when x86 is not an IF/MYIF (to save time).
(defthmd run-until-esp-is-above-base-axe
  (implies (and (axe-syntaxp (not (syntactic-call-of 'if x86 dag-array)))
                ;; (axe-syntaxp (not (syntactic-call-of 'myif x86 dag-array))) ; may be needed someday
                (esp-is-abovep old-esp x86))
           (equal (run-until-esp-is-above old-esp x86)
                  x86))
  :hints (("Goal" :in-theory (enable run-until-esp-is-above-base))))

;; For use by Axe.
;; Only fires when x86 is not an IF/MYIF (so we don't need IF lifting rules for x86-fetch-decode-execute and its subfunctions).
(defthmd run-until-esp-is-above-opener-axe
  (implies (and (axe-syntaxp (not (syntactic-call-of 'if x86 dag-array)))
                ;; (axe-syntaxp (not (syntactic-call-of 'myif x86 dag-array))) ; may be needed someday
                (not (esp-is-abovep old-esp x86)))
           (equal (run-until-esp-is-above old-esp x86)
                  (run-until-esp-is-above old-esp (x86-fetch-decode-execute x86))))
  :hints (("Goal" :in-theory (enable run-until-esp-is-above-opener))))

;; For use by Axe.
;; Only fires when x86 is not an IF/MYIF (to save time).
(defthmd run-until-esp-is-above-or-reach-pc-base-axe
  (implies (and (axe-syntaxp (not (syntactic-call-of 'if x86 dag-array)))
                ;; (axe-syntaxp (not (syntactic-call-of 'myif x86 dag-array))) ; may be needed someday
                (or (esp-is-abovep old-esp x86)
                    (member-equal (rip x86) stop-pcs)))
           (equal (run-until-esp-is-above-or-reach-pc old-esp stop-pcs x86)
                  x86))
  :hints (("Goal" :in-theory (enable run-until-esp-is-above-or-reach-pc-base))))

;; For use by Axe.
;; Only fires when x86 is not an IF/MYIF (so we don't need IF lifting rules for x86-fetch-decode-execute and its subfunctions).
(defthmd run-until-esp-is-above-or-reach-pc-opener-axe
  (implies (and (axe-syntaxp (not (syntactic-call-of 'if x86 dag-array)))
                ;; (axe-syntaxp (not (syntactic-call-of 'myif x86 dag-array))) ; may be needed someday
                (not (esp-is-abovep old-esp x86))
                (not (member-equal (rip x86) stop-pcs)))
           (equal (run-until-esp-is-above-or-reach-pc old-esp stop-pcs x86)
                  (run-until-esp-is-above-or-reach-pc old-esp stop-pcs (x86-fetch-decode-execute x86))))
  :hints (("Goal" :in-theory (enable run-until-esp-is-above-or-reach-pc-opener))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; probably only needed for axe
(defthmd integerp-of-ctri
  (integerp (ctri i x86)))

;; probably only needed for axe
(defthmd booleanp-of-canonical-address-p (booleanp (canonical-address-p lin-addr)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Warning: Do not prove a rule to open this on non-constants, even though it is provably always true.
;; We arrange for (poor-mans-quotep x) to be rewritten to true only if x is a quoted constant.
(defund poor-mans-quotep (x) (declare (ignore x)) t)
(def-constant-opener poor-mans-quotep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Only opens x86-fetch-decode-execute if we can resolve the (first byte of) the current instruction to a constant
;; Creates x86-fetch-decode-execute-base-new.
;; We tried just testing whether RIP is a constant, but sometimes RIP can be the variable TEXT-OFFSET.
;; Could simplify this for 64-bit mode (use rip and read) but then what about 32-bit mode?
;; ttodo: try using a binding hyp for proc-mode
(defopeners x86-fetch-decode-execute :suffix -new
  :hyps (;(poor-mans-quotep (rip x86))
         ;;(canonical-address-p (rip x86)) ; could drop, but this clarifies failures
         (canonical-address-p (let ((proc-mode (x86-operation-mode x86)))
                                (read-*ip proc-mode x86))) ; could drop, but this clarifies failures
         ;; ;; Requires us to be able to read the byte at the RIP:
         (poor-mans-quotep (let ((proc-mode (x86-operation-mode x86)))
                             (mv-nth 1 (rme08$inline proc-mode (read-*ip proc-mode x86) 1 :x x86))))
         ;; (poor-mans-quotep (let ((proc-mode (x86-operation-mode x86)))
         ;;                     (read 1 (read-*ip proc-mode x86) x86)))
         ;; (poor-mans-quotep (read 1 (rip x86) x86))
         (not (ms x86))
         (not (fault x86))))

;; should be faster?
;; todo: continue specializing to 64-bit mode
(defthmd x86-fetch-decode-execute-opener-safe-64
  (implies (and (canonical-address-p (read-*ip 0 x86)) ; could drop, but this clarifies failures
                ;; ;; Requires us to be able to read the byte at the RIP:
                ;; todo: simplify this:
                (poor-mans-quotep (mv-nth 1 (rme08$inline 0 (read-*ip 0 x86) 1 :x x86))) ;  todo: use a binding hyp?
                ;; (poor-mans-quotep (let ((proc-mode (x86-operation-mode x86)))
                ;;                     (read 1 (read-*ip proc-mode x86) x86)))
                ;; (poor-mans-quotep (read 1 (rip x86) x86))
                (64-bit-modep x86)
                (app-view x86)
                (not (ms x86))
                (not (fault x86)))
           (equal (x86-fetch-decode-execute x86)
                  (let* ( ;(__function__ 'x86-fetch-decode-execute)
                         (ctx 'x86-fetch-decode-execute))
                    ;; (if (or (ms x86) (fault x86)) ; known false above
                    ;;     x86
                    (let* ((proc-mode 0 ;(x86-operation-mode x86)
                                      ) ; todo: build these in!
                           (64-bit-modep t ;
                                         ;(equal proc-mode 0)
                                         )
                             (start-rip (read-*ip proc-mode x86)))
                        (mv-let (flg acl2::|(THE (UNSIGNED-BYTE 52) PREFIXES)|
                                     acl2::|(THE (UNSIGNED-BYTE 8) REX-BYTE)|
                                     x86)
                          (get-prefixes proc-mode start-rip 0 0 15 x86)
                          (let* ((prefixes acl2::|(THE (UNSIGNED-BYTE 52) PREFIXES)|)
                                 (rex-byte acl2::|(THE (UNSIGNED-BYTE 8) REX-BYTE)|))
                            (if flg (!ms (let ((x86isa::erp nil))
                                           (cons (list ctx
                                                       :rip (x86isa::rip x86)
                                                       :error-in-reading-prefixes flg)
                                                 x86isa::erp))
                                         x86)
                              (let* ((x86isa::opcode/vex/evex-byte (x86isa::prefixes->nxt prefixes))
                                     (x86isa::prefix-length (x86isa::prefixes->num prefixes)))
                                (mv-let (flg temp-rip)
                                  (x86isa::add-to-*ip proc-mode
                                                      start-rip (+ 1 x86isa::prefix-length)
                                                      x86)
                                  (if flg (!ms (let ((x86isa::erp nil))
                                                 (cons (list ctx
                                                             :rip (x86isa::rip x86)
                                                             :increment-error flg)
                                                       x86isa::erp))
                                               x86)
                                    (let ((x86isa::vex-byte0? (or (equal x86isa::opcode/vex/evex-byte 197)
                                                                  (equal x86isa::opcode/vex/evex-byte 196))))
                                      (mv-let (flg x86isa::les/lds-distinguishing-byte x86)
                                        (if x86isa::vex-byte0? (x86isa::rme08 proc-mode temp-rip 1
                                                                              :x x86)
                                          (mv nil 0 x86))
                                        (cond (flg (!ms (let ((x86isa::erp nil))
                                                          (cons (list ctx
                                                                      :rip (x86isa::rip x86)
                                                                      :les/lds-distinguishing-byte-read-error flg)
                                                                x86isa::erp))
                                                        x86))
                                              ((and x86isa::vex-byte0?
                                                    (or 64-bit-modep
                                                        (equal (bitops::part-select-low-high x86isa::les/lds-distinguishing-byte 6 7)
                                                               3)))
                                               (mv-let (flg temp-rip)
                                                 (x86isa::add-to-*ip proc-mode temp-rip 1 x86)
                                                 (if flg (!ms (let ((x86isa::erp nil))
                                                                (cons (list ctx
                                                                            :rip (x86isa::rip x86)
                                                                            :vex-byte1-increment-error flg)
                                                                      x86isa::erp))
                                                              x86)
                                                   (let* ((x86isa::vex-prefixes (x86isa::!vex-prefixes->byte0 x86isa::opcode/vex/evex-byte 0))
                                                          (x86isa::vex-prefixes (x86isa::!vex-prefixes->byte1 x86isa::les/lds-distinguishing-byte
                                                                                                              x86isa::vex-prefixes)))
                                                     (x86isa::vex-decode-and-execute proc-mode start-rip temp-rip prefixes
                                                                                     rex-byte x86isa::vex-prefixes x86)))))
                                              (t (let* ((x86isa::opcode/evex-byte x86isa::opcode/vex/evex-byte)
                                                        (x86isa::evex-byte0? (equal x86isa::opcode/evex-byte 98)))
                                                   (mv-let (flg x86isa::bound-distinguishing-byte x86)
                                                     (if x86isa::evex-byte0? (x86isa::rme08 proc-mode temp-rip 1
                                                                                            :x x86)
                                                       (mv nil 0 x86))
                                                     (cond (flg (!ms (let ((x86isa::erp nil))
                                                                       (cons (list ctx
                                                                                   :rip (x86isa::rip x86)
                                                                                   :bound-distinguishing-byte-read-error flg)
                                                                             x86isa::erp))
                                                                     x86))
                                                           ((and x86isa::evex-byte0?
                                                                 (or 64-bit-modep
                                                                     (equal (bitops::part-select-low-high x86isa::bound-distinguishing-byte 6 7)
                                                                            3)))
                                                            (mv-let (flg temp-rip)
                                                              (x86isa::add-to-*ip proc-mode temp-rip 1 x86)
                                                              (if flg (!ms (let ((x86isa::erp nil))
                                                                             (cons (list ctx
                                                                                         :rip (x86isa::rip x86)
                                                                                         :evex-byte1-increment-error flg)
                                                                                   x86isa::erp))
                                                                           x86)
                                                                (let* ((x86isa::evex-prefixes (x86isa::!evex-prefixes->byte0 x86isa::opcode/evex-byte 0))
                                                                       (x86isa::evex-prefixes (x86isa::!evex-prefixes->byte1 x86isa::bound-distinguishing-byte
                                                                                                                             x86isa::evex-prefixes)))
                                                                  (x86isa::evex-decode-and-execute proc-mode start-rip temp-rip prefixes
                                                                                                   rex-byte x86isa::evex-prefixes x86)))))
                                                           (t (let* ((x86isa::opcode-byte x86isa::opcode/evex-byte)
                                                                     (x86isa::modr/m? (x86isa::one-byte-opcode-modr/m-p proc-mode x86isa::opcode-byte)))
                                                                (mv-let (flg acl2::|(THE (UNSIGNED-BYTE 8) MODR/M)|
                                                                             x86)
                                                                  (if x86isa::modr/m? (if (or x86isa::vex-byte0? x86isa::evex-byte0?)
                                                                                          (mv nil
                                                                                              x86isa::les/lds-distinguishing-byte x86)
                                                                                        (x86isa::rme08 proc-mode temp-rip 1
                                                                                                       :x x86))
                                                                    (mv nil 0 x86))
                                                                  (let ((modr/m acl2::|(THE (UNSIGNED-BYTE 8) MODR/M)|))
                                                                    (if flg (!ms (let ((x86isa::erp nil))
                                                                                   (cons (list ctx
                                                                                               :rip (x86isa::rip x86)
                                                                                               :modr/m-byte-read-error flg)
                                                                                         x86isa::erp))
                                                                                 x86)
                                                                      (mv-let (flg temp-rip)
                                                                        (if x86isa::modr/m? (x86isa::add-to-*ip proc-mode temp-rip 1 x86)
                                                                          (mv nil temp-rip))
                                                                        (if flg (!ms (let ((x86isa::erp nil))
                                                                                       (cons (list ctx
                                                                                                   :rip (x86isa::rip x86)
                                                                                                   :increment-error flg)
                                                                                             x86isa::erp))
                                                                                     x86)
                                                                          (let ((x86isa::sib? (and x86isa::modr/m?
                                                                                                   (let* ((x86isa::p4? (eql 103 (x86isa::prefixes->adr prefixes)))
                                                                                                          (x86isa::16-bit-addressp (eql 2
                                                                                                                                        (x86isa::select-address-size proc-mode x86isa::p4? x86))))
                                                                                                     (x86isa::x86-decode-sib-p modr/m x86isa::16-bit-addressp)))))
                                                                            (mv-let (flg acl2::|(THE (UNSIGNED-BYTE 8) SIB)| x86)
                                                                              (if x86isa::sib? (x86isa::rme08 proc-mode temp-rip 1
                                                                                                              :x x86)
                                                                                (mv nil 0 x86))
                                                                              (let ((sib acl2::|(THE (UNSIGNED-BYTE 8) SIB)|))
                                                                                (if flg (!ms (let ((x86isa::erp nil))
                                                                                               (cons (list ctx
                                                                                                           :rip (x86isa::rip x86)
                                                                                                           :sib-byte-read-error flg)
                                                                                                     x86isa::erp))
                                                                                             x86)
                                                                                  (mv-let (flg temp-rip)
                                                                                    (if x86isa::sib? (x86isa::add-to-*ip proc-mode temp-rip 1 x86)
                                                                                      (mv nil temp-rip))
                                                                                    (if flg (!ms (let ((x86isa::erp nil))
                                                                                                   (cons (list ctx
                                                                                                               :rip (x86isa::rip x86)
                                                                                                               :increment-error flg)
                                                                                                         x86isa::erp))
                                                                                                 x86)
                                                                                      (one-byte-opcode-execute proc-mode start-rip temp-rip prefixes
                                                                                                               rex-byte x86isa::opcode-byte modr/m
                                                                                                               sib x86))))))))))))))))))))))))))))
                    ;)
                    )))
  :hints (("Goal" :in-theory (enable x86-fetch-decode-execute
                                     x86-operation-mode))))

(defopeners bv-array-read-chunk-little)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; An alias of clear
(defund clear-extend (n addr x86)
  (declare (xargs :guard (and (natp n)
                              (integerp addr))
                  :stobjs x86))
  (write n addr 0 x86))

;; An alias of clear
(defund clear-retract (n addr x86)
  (declare (xargs :guard (and (natp n)
                              (integerp addr))
                  :stobjs x86))
  (write n addr 0 x86))

;; Introduces the clear when there is a write in X86 to be cleared.
;; For Axe only
(defthmd write-becomes-write-of-clear-extend-axe
  (implies (and (axe-syntaxp (write-with-addr-and-size-presentp-axe n ad x86 acl2::dag-array))
               ; (integerp ad)
                (unsigned-byte-p 48 n))
           (equal (write n ad val x86)
                  (write n ad val (clear-extend n ad x86))))
  :hints (("Goal" :in-theory (enable clear-extend))))

;; Copies the clear inside a write that is not its target
;; For Axe only
(defthmd clear-extend-of-write-continue-axe
  (implies (and (axe-syntaxp (and (syntactic-call-of 'write x86 dag-array) ; avoid loops and undesired patterns
                                  (not (and (acl2::dargs-equalp n1 n2 dag-array)
                                            (acl2::dargs-equalp ad1 ad2 dag-array)))))
                ;(integerp ad1)
                (unsigned-byte-p 48 n1)
                ;(integerp ad2)
                (unsigned-byte-p 48 n2))
           (equal (clear-extend n1 ad1 (write n2 ad2 val x86))
                  (clear-extend n1 ad1 (write n2 ad2 val (clear-extend n1 ad1 x86)))))
  :hints (("Goal" :cases ((integerp ad1)) ; todo: generalize write-of-write-of-write-same
           :in-theory (enable clear-extend))))

;; We've found the write to be cleared
(defthmd clear-extend-of-write-finish
  (implies (and ;(integerp ad)
                (unsigned-byte-p 48 n))
           (equal (clear-extend n ad (write n ad val x86))
                  (clear-retract n ad x86)))
  :hints (("Goal" :in-theory (enable clear-extend clear-retract))))

(defthmd clear-extend-of-write-of-clear-retract
  (implies (and; (integerp ad1)
                (unsigned-byte-p 48 n1)
                ;(integerp ad2)
                (unsigned-byte-p 48 n2))
           (equal (clear-extend n1 ad1 (write n2 ad2 val (clear-retract n1 ad1 x86)))
                  (clear-retract n1 ad1 (write n2 ad2 val x86))))
  :hints (("Goal" :cases ((integerp ad1))
           :in-theory (enable clear-retract clear-extend))))

(defthmd write-of-clear-retract ; add -same to name
  (implies (and ;(integerp ad)
                (unsigned-byte-p 48 n))
           (equal (write n ad val (clear-retract n ad x86))
                  (write n ad val x86)))
  :hints (("Goal" :in-theory (enable clear-retract))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A scheme for removing set-flag in (read (write ... (write (set-flag ...))))

(defund clear-flags-extend (x86)
  (declare (xargs :stobjs x86))
  (!rflags 0 x86))

(defund clear-flags-retract (x86)
  (declare (xargs :stobjs x86))
  (!rflags 0 x86))

;; Introduces the clear when there is a set-flag inside the write nest
;; For Axe only
(defthmd read-of-write-becomes-read-of-write-of-clear-flags-extend-axe
  (implies (axe-syntaxp (write-nest-with-inner-set-flagp-axe x86 acl2::dag-array))
           (equal (read n ad (write n2 ad2 val x86))
                  (read n ad (write n2 ad2 val (clear-flags-extend x86)))))
  :hints (("Goal" :in-theory (e/d (clear-flags-extend write-of-!rflags) (!rflags !rflags-of-write)))))

;; Copies the clear inside a write that is not its target
;; For Axe only
(defthmd clear-flags-extend-of-write-continue-axe
  (implies (axe-syntaxp (or (syntactic-call-of 'write x86 dag-array) ; avoid loops and undesired patterns
                            (syntactic-call-of 'set-flag x86 dag-array)))
           (equal (clear-flags-extend (write n ad val x86))
                  (clear-flags-extend (write n ad val (clear-flags-extend x86)))))
  :hints (("Goal" :in-theory (enable clear-flags-extend))))

;; We've found the write to be cleared
(defthmd clear-flags-extend-of-set-flag-finish
  (equal (clear-flags-extend (set-flag flag val x86))
         (clear-flags-retract x86))
  :hints (("Goal" :in-theory (enable clear-flags-extend clear-flags-retract))))

(defthmd clear-flags-extend-of-write-of-clear-flags-retract
  (equal (clear-flags-extend (write n ad val (clear-flags-retract x86)))
         (clear-flags-retract (write n ad val x86)))
  :hints (("Goal" :in-theory (enable clear-flags-retract clear-flags-extend))))

(defthmd read-of-write-of-clear-flags-retract ; add -same to name
  (equal (read n ad (write n2 ad2 val (clear-flags-retract x86)))
         (read n ad (write n2 ad2 val x86)))
  :hints (("Goal" :in-theory (enable clear-flags-retract))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Reorders writes to try to bring adjacent writes together:
(defthm write-of-write-diff-bv-axe
  (implies (and (axe-syntaxp (addresses-out-of-orderp ad1 ad2 dag-array))
                (bvle 48 n2 (bvminus 48 ad1 ad2))
                (bvle 48 n1 (bvminus 48 ad2 ad1))
                (unsigned-byte-p 48 n2) ;; (natp n2)
                (unsigned-byte-p 48 n1) ;; (natp n1)
                (integerp ad2)
                (integerp ad1))
           (equal (write n1 ad1 val1 (write n2 ad2 val2 x86))
                  (write n2 ad2 val2 (write n1 ad1 val1 x86))))
  :hints (("Goal" :use write-of-write-diff-bv
           :in-theory (disable write-of-write-diff-bv))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; this puts the syntactically smaller op first
(defthmd equal-of-0-and-mv-nth-1-of-sse-cmp-of-ucomi-reorder-axe
  (implies (and (axe-syntaxp (acl2::lighter-dargp op2 op1))
                (equal (mxcsrbits->daz mxcsr) 0)
                (equal (mxcsrbits->im mxcsr) 1)
                (equal (mxcsrbits->dm mxcsr) 1))
           (equal (equal 0 (mv-nth 1 (sse-cmp *op-ucomi* op1 op2 mxcsr exp-width frac-width)))
                  (equal 1 (mv-nth 1 (sse-cmp *op-ucomi* op2 op1 mxcsr exp-width frac-width)))))
  :hints (("Goal" :use equal-of-0-and-mv-nth-1-of-sse-cmp-of-ucomi-reorder)))

;; this puts the syntactically smaller op first
(defthmd equal-of-1-and-mv-nth-1-of-sse-cmp-of-ucomi-reorder-axe
  (implies (and (axe-syntaxp (acl2::lighter-dargp op2 op1))
                (equal (mxcsrbits->daz mxcsr) 0)
                (equal (mxcsrbits->im mxcsr) 1)
                (equal (mxcsrbits->dm mxcsr) 1))
           (equal (equal 1 (mv-nth 1 (sse-cmp *op-ucomi* op1 op2 mxcsr exp-width frac-width)))
                  (equal 0 (mv-nth 1 (sse-cmp *op-ucomi* op2 op1 mxcsr exp-width frac-width)))))
  :hints (("Goal" :use equal-of-1-and-mv-nth-1-of-sse-cmp-of-ucomi-reorder)))

;; this puts the syntactically smaller op first
(defthmd equal-of-7-and-mv-nth-1-of-sse-cmp-of-ucomi-reorder-axe
  (implies (axe-syntaxp (acl2::lighter-dargp op2 op1))
           (equal (equal 7 (mv-nth 1 (sse-cmp *op-ucomi* op1 op2 mxcsr exp-width frac-width)))
                  (equal 7 (mv-nth 1 (sse-cmp *op-ucomi* op2 op1 mxcsr exp-width frac-width)))))
  :hints (("Goal" :use equal-of-7-and-mv-nth-1-of-sse-cmp-of-ucomi-reorder)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd read-of-write-irrel-bv-axe
  (implies (and (axe-smt (bvle 48 n2 (bvminus 48 addr1 addr2)))
                (axe-smt (bvle 48 n1 (bvminus 48 addr2 addr1)))
                (unsigned-byte-p 48 n1)
                (unsigned-byte-p 48 n2))
           (equal (read n1 addr1 (write n2 addr2 val x86))
                  (read n1 addr1 x86)))
  :hints (("Goal" :use (:instance read-of-write-irrel-gen)
           :in-theory (e/d (bvlt) (read-of-write-irrel-gen)))))

(defthmd canonical-address-p-when-bvlt-of-bvplus-axe
  (implies (and (signed-byte-p 64 x)
                (axe-smt (bvlt 64 (bvplus 64 140737488355328 x) 281474976710656)))
           (canonical-address-p x))
  :hints (("Goal" :cases ((< x 0))
           :in-theory (enable canonical-address-p bvlt signed-byte-p
                              acl2::bvchop-when-negative-lemma))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; todo: replace.  same for other registers?
(defthm integerp-of-rsp-gen
  (integerp (rsp x86))
  :hints (("Goal" :in-theory (enable rsp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd signed-byte-p-of-+-when-canonical-and-canonical
  (implies (and (canonical-address-p x) ; could restrict to constant x
                (canonical-address-p y))
           (signed-byte-p 64 (+ x y))))

(defthmd logext-64-of-+-when-canonical-and-canonical
  (implies (and (canonical-address-p x) ; could restrict to constant x
                (canonical-address-p y))
           (equal (logext 64 (+ x y))
                  (+ x y))))

(defthm signed-byte-p-of-xr-of-rip
  (implies (and (<= 48 n)
                (integerp n))
           (signed-byte-p n (xr :rip nil x86)))
  :hints (("Goal" :use (:instance x86isa::i48p-xr-rip (i nil))
           :in-theory (e/d (x86isa::rip) (x86isarip-becomes-rip
                                          xr-becomes-rip
                                          x86isa::i48p-xr-rip
                                          x86isa::elem-p-of-xr-rip)))))

(defthm signed-byte-p-of-rip
  (implies (and (<= 48 n)
                (integerp n))
           (signed-byte-p n (x86isa::rip x86)))
  :hints (("Goal" :in-theory (e/d (x86isa::rip)
                                  (x86isarip-becomes-rip
                                   xr-becomes-rip
                                   )))))

(defthm x86isa::canonical-address-p-of-rip
  (canonical-address-p (x86isa::rip x86))
  :hints (("Goal" :in-theory (enable canonical-address-p$inline))))

;; used in the loop-lifter?
(defthm x86isa::canonical-address-p-of-xr-of-rip
  (canonical-address-p (xr :rip nil x86))
  :hints (("Goal" :in-theory (enable canonical-address-p$inline))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm integerp-of-!rflagsbits->af (integerp (!rflagsbits->af af rflags)))
(defthm integerp-of-!rflagsbits->cf (integerp (!rflagsbits->cf cf rflags)))
(defthm integerp-of-!rflagsbits->of (integerp (!rflagsbits->of of rflags)))
(defthm integerp-of-!rflagsbits->pf (integerp (!rflagsbits->pf pf rflags)))
(defthm integerp-of-!rflagsbits->sf (integerp (!rflagsbits->sf sf rflags)))
(defthm integerp-of-!rflagsbits->zf (integerp (!rflagsbits->zf zf rflags)))
(defthm integerp-of-!rflagsbits->res1 (integerp (!rflagsbits->res1 res1 rflags)))
(defthm integerp-of-!rflagsbits->res2 (integerp (!rflagsbits->res2 res2 rflags)))
(defthm integerp-of-!rflagsbits->res3 (integerp (!rflagsbits->res3 res3 rflags)))
