; Support for using Axe to reason about x86 code
;
; Copyright (C) 2016-2019 Kestrel Technology, LLC
; Copyright (C) 2020-2024 Kestrel Institute
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
(include-book "kestrel/x86/run-until-return" :dir :system)
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

(add-known-boolean x86isa::cr0bits-p$inline)
(add-known-boolean x86isa::cr3bits-p$inline)
(add-known-boolean x86isa::cr4bits-p$inline)
(add-known-boolean x86isa::cr8bits-p$inline)

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
                  (acl2::lookup-equal n l)))
  :hints (("Goal" :in-theory (enable acl2::lookup-equal aref1))))

(defopeners x86isa::64-bit-mode-two-byte-opcode-modr/m-p
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

(def-constant-opener acl2::bool->bit$inline)
(def-constant-opener acl2::rotate-left)
(def-constant-opener acl2::rotate-right)

;; Flag-related functions (these seem safe to execute without that requiring
;; more rules; for example, we expect jle-condition to always be called on flag
;; functions with the same arguments (dst and src), so either all the args to
;; jle-condition get evaluated or none of them do).

(def-constant-opener x86isa::zf-spec$inline)

(def-constant-opener x86isa::cf-spec8$inline)
(def-constant-opener x86isa::of-spec8$inline)
(def-constant-opener x86isa::pf-spec8$inline)
(def-constant-opener x86isa::sf-spec8$inline)
(def-constant-opener x86isa::adc-af-spec8$inline)
(def-constant-opener x86isa::add-af-spec8$inline)
(def-constant-opener x86isa::sub-af-spec8$inline)
(def-constant-opener x86isa::sub-cf-spec8) ; todo: make these inline, like the others
(def-constant-opener x86isa::sub-of-spec8)
(def-constant-opener x86isa::sub-pf-spec8)
(def-constant-opener x86isa::sub-sf-spec8)
(def-constant-opener x86isa::sub-zf-spec8)

(def-constant-opener x86isa::cf-spec16$inline)
(def-constant-opener x86isa::of-spec16$inline)
(def-constant-opener x86isa::pf-spec16$inline)
(def-constant-opener x86isa::sf-spec16$inline)
(def-constant-opener x86isa::adc-af-spec16$inline)
(def-constant-opener x86isa::add-af-spec16$inline)
(def-constant-opener x86isa::sub-af-spec16$inline)
(def-constant-opener x86isa::sub-cf-spec16)
(def-constant-opener x86isa::sub-of-spec16)
(def-constant-opener x86isa::sub-pf-spec16)
(def-constant-opener x86isa::sub-sf-spec16)
(def-constant-opener x86isa::sub-zf-spec16)

(def-constant-opener x86isa::cf-spec32$inline)
(def-constant-opener x86isa::of-spec32$inline)
(def-constant-opener x86isa::pf-spec32$inline)
(def-constant-opener x86isa::sf-spec32$inline)
(def-constant-opener x86isa::adc-af-spec32$inline)
(def-constant-opener x86isa::add-af-spec32$inline)
(def-constant-opener x86isa::sub-af-spec32$inline)
(def-constant-opener x86isa::sub-cf-spec32)
(def-constant-opener x86isa::sub-of-spec32)
(def-constant-opener x86isa::sub-pf-spec32)
(def-constant-opener x86isa::sub-sf-spec32)
(def-constant-opener x86isa::sub-zf-spec32)

(def-constant-opener x86isa::cf-spec64$inline)
(def-constant-opener x86isa::of-spec64$inline)
(def-constant-opener x86isa::pf-spec64$inline)
(def-constant-opener x86isa::sf-spec64$inline)
(def-constant-opener x86isa::adc-af-spec64$inline)
(def-constant-opener x86isa::add-af-spec64$inline)
(def-constant-opener x86isa::sub-af-spec64$inline)
(def-constant-opener x86isa::sub-cf-spec64)
(def-constant-opener x86isa::sub-of-spec64)
(def-constant-opener x86isa::sub-pf-spec64)
(def-constant-opener x86isa::sub-sf-spec64)
(def-constant-opener x86isa::sub-zf-spec64)

(def-constant-opener x86isa::!rflagsbits->ac$inline)
(def-constant-opener x86isa::!rflagsbits->af$inline)
(def-constant-opener x86isa::!rflagsbits->cf$inline)
(def-constant-opener x86isa::!rflagsbits->of$inline)
(def-constant-opener x86isa::!rflagsbits->pf$inline)
(def-constant-opener x86isa::!rflagsbits->sf$inline)
(def-constant-opener x86isa::!rflagsbits->zf$inline)

(def-constant-opener x86isa::one-byte-opcode-modr/m-p$inline)
(def-constant-opener x86isa::two-byte-opcode-modr/m-p$inline)

(def-constant-opener x86isa::rflagsbits->ac$inline)
(def-constant-opener x86isa::rflagsbits->af$inline)
(def-constant-opener x86isa::rflagsbits->cf$inline)
(def-constant-opener x86isa::rflagsbits->of$inline)
(def-constant-opener x86isa::rflagsbits->pf$inline)
(def-constant-opener x86isa::rflagsbits->sf$inline)
(def-constant-opener x86isa::rflagsbits->zf$inline)
(def-constant-opener x86isa::rflagsbits->res1$inline)
(def-constant-opener x86isa::rflagsbits->res2$inline)
(def-constant-opener x86isa::rflagsbits->res3$inline)

(def-constant-opener x86isa::rflagsbits->tf$inline)
(def-constant-opener x86isa::rflagsbits->intf$inline)
(def-constant-opener x86isa::rflagsbits->df$inline)
(def-constant-opener x86isa::rflagsbits->iopl$inline)
(def-constant-opener x86isa::rflagsbits->nt$inline)
(def-constant-opener x86isa::rflagsbits->res4$inline)
(def-constant-opener x86isa::rflagsbits->rf$inline)
(def-constant-opener x86isa::rflagsbits->vm$inline)
(def-constant-opener x86isa::rflagsbits->vif$inline)
(def-constant-opener x86isa::rflagsbits->vip$inline)
(def-constant-opener x86isa::rflagsbits->id$inline)
(def-constant-opener x86isa::rflagsbits->res5$inline)
(def-constant-opener x86isa::rflagsbits$inline)

(def-constant-opener x86isa::!rflagsbits->af$inline)

(def-constant-opener x86isa::10bits-fix)
(def-constant-opener x86isa::2bits-fix)
(def-constant-opener acl2::expt2$inline)

(def-constant-opener X86ISA::RFLAGSBITS-FIX$INLINE)

(def-constant-opener x86isa::feature-flags); needed?

(def-constant-opener x86isa::32-bit-mode-two-byte-opcode-modr/m-p)
(def-constant-opener x86isa::32-bit-compute-mandatory-prefix-for-two-byte-opcode$inline)

;; TODO: Think about whether to use regular rules, constant opener rules, or build into the evaluator.

(def-constant-opener x86isa::prefixes->num$inline)
(def-constant-opener x86isa::prefixes->lck$inline)
(def-constant-opener x86isa::prefixes->rep$inline)
(def-constant-opener x86isa::prefixes->seg$inline)
(def-constant-opener x86isa::prefixes->opr$inline)
(def-constant-opener x86isa::prefixes->adr$inline)
(def-constant-opener x86isa::prefixes->nxt$inline)

(def-constant-opener x86isa::!prefixes->rep$inline)
(def-constant-opener x86isa::!prefixes->seg$inline)

(def-constant-opener x86isa::evex-prefixes->byte0$inline)
(def-constant-opener x86isa::evex-prefixes->byte1$inline)
(def-constant-opener x86isa::evex-prefixes->byte2$inline)
(def-constant-opener x86isa::evex-prefixes->byte3$inline)

(def-constant-opener x86isa::!evex-prefixes->byte0$inline)
(def-constant-opener x86isa::!evex-prefixes->byte1$inline)
(def-constant-opener x86isa::!evex-prefixes->byte2$inline)
(def-constant-opener x86isa::!evex-prefixes->byte3$inline)

(def-constant-opener x86isa::vex-prefixes-fix$inline)
(def-constant-opener x86isa::vex-prefixes->byte0$inline)
(def-constant-opener x86isa::vex-prefixes->byte1$inline)
(def-constant-opener x86isa::vex-prefixes->byte2$inline)
(def-constant-opener x86isa::!vex-prefixes->byte0$inline)
(def-constant-opener x86isa::!vex-prefixes->byte1$inline)
(def-constant-opener x86isa::!vex-prefixes->byte2$inline)
(def-constant-opener x86isa::vex-opcode-modr/m-p$inline)
(def-constant-opener x86isa::vex-prefixes-map-p$inline)

(def-constant-opener x86isa::evex-byte1->mmm$inline)
(def-constant-opener x86isa::evex-byte1->res$inline)
(def-constant-opener x86isa::evex-byte1->r-prime$inline)
(def-constant-opener x86isa::evex-byte1->b$inline)
(def-constant-opener x86isa::evex-byte1->x$inline)
(def-constant-opener x86isa::evex-byte1->r$inline)

(def-constant-opener x86isa::evex-byte2->pp$inline)
(def-constant-opener x86isa::evex-byte2->res$inline)
(def-constant-opener x86isa::evex-byte2->vvvv$inline)
(def-constant-opener x86isa::evex-byte2->w$inline)

(def-constant-opener x86isa::evex-byte3->aaa$inline)
(def-constant-opener x86isa::evex-byte3->v-prime$inline)
(def-constant-opener x86isa::evex-byte3->b$inline)
(def-constant-opener x86isa::evex-byte3->vl/rc$inline)
(def-constant-opener x86isa::evex-byte3->z$inline)

(def-constant-opener x86isa::vex->vvvv$inline)
(def-constant-opener x86isa::vex->l$inline)
(def-constant-opener x86isa::vex->pp$inline)
(def-constant-opener x86isa::vex->r$inline)
(def-constant-opener x86isa::vex->w$inline)
(def-constant-opener x86isa::vex->b$inline)
(def-constant-opener x86isa::vex->x$inline)

(def-constant-opener x86isa::vex2-byte1-fix$inline)
(def-constant-opener x86isa::vex2-byte1->pp$inline)
(def-constant-opener x86isa::vex2-byte1->l$inline)
(def-constant-opener x86isa::vex2-byte1->vvvv$inline)
(def-constant-opener x86isa::vex2-byte1->r$inline)

;; can we optimize these by avoiding introducing the fix?
(def-constant-opener x86isa::vex3-byte1-fix$inline)
(def-constant-opener x86isa::vex3-byte1->m-mmmm$inline)
(def-constant-opener x86isa::vex3-byte1->b$inline)
(def-constant-opener x86isa::vex3-byte1->x$inline)
(def-constant-opener x86isa::vex3-byte1->r$inline)

(def-constant-opener x86isa::vex3-byte2-fix$inline)
(def-constant-opener x86isa::vex3-byte2->pp$inline)
(def-constant-opener x86isa::vex3-byte2->l$inline)
(def-constant-opener x86isa::vex3-byte2->vvvv$inline)
(def-constant-opener x86isa::vex3-byte2->w$inline)

(def-constant-opener x86isa::rex-byte-from-vex-prefixes)

(def-constant-opener x86isa::vex-vvvv-reg-index)

(def-constant-opener canonical-address-p$inline)

;(defopeners byte-ify :hyps ((syntaxp (and (quotep n) (quotep val)))))

(def-constant-opener byte-listp)

(def-constant-opener x86isa::mxcsrbits-fix)

;; these expose part-select
(def-constant-opener x86isa::mxcsrbits->ie$inline)
(def-constant-opener x86isa::mxcsrbits->de$inline)
(def-constant-opener x86isa::mxcsrbits->ze$inline)
(def-constant-opener x86isa::mxcsrbits->oe$inline)
(def-constant-opener x86isa::mxcsrbits->ue$inline)
(def-constant-opener x86isa::mxcsrbits->pe$inline)
(def-constant-opener x86isa::mxcsrbits->daz$inline)
(def-constant-opener x86isa::mxcsrbits->im$inline)
(def-constant-opener x86isa::mxcsrbits->dm$inline)
(def-constant-opener x86isa::mxcsrbits->zm$inline)
(def-constant-opener x86isa::mxcsrbits->om$inline)
(def-constant-opener x86isa::mxcsrbits->um$inline)
(def-constant-opener x86isa::mxcsrbits->pm$inline)
(def-constant-opener x86isa::mxcsrbits->rc$inline)
(def-constant-opener x86isa::mxcsrbits->ftz$inline)
(def-constant-opener x86isa::mxcsrbits->reserved$inline)

(def-constant-opener x86isa::convert-arith-operation-to-rtl-op$inline)
;(def-constant-opener x86isa::feature-flag) ; keep feature-flag disabled, for clarity
;(def-constant-opener x86isa::cpuid-flag-fn) ; can't do this, it's an encapsulate
(def-constant-opener rtl::set-flag) ; drop?

(defopeners acl2::get-symbol-entry-mach-o)
(defopeners acl2::get-all-sections-from-mach-o-load-commands)
(defopeners acl2::get-section-number-mach-o-aux)

(defopeners addresses-of-subsequent-stack-slots-aux)

(defopeners acl2::get-pe-section-aux)
(defopeners acl2::lookup-pe-symbol)

(defopeners x86isa::simd-add-spec)
(defopeners x86isa::simd-sub-spec)

;; ;todo
;; (thm
;;  (equal (bitops::rotate-left-32 x places)
;;         (acl2::leftrotate32 places x))
;;  :hints (("Goal" :in-theory (enable bitops::rotate-left-32 ACL2::ROTATE-LEFT acl2::leftrotate32 acl2::leftrotate))))

(defthm set-flag-of-set-flag-diff-axe
  (implies (and (syntaxp (and (quotep flag1)
                              (quotep flag2)
                              ))
                (axe-syntaxp (heavier-dag-term flag1 flag2))
                (not (equal flag1 flag2))
                (member-eq flag1 *flags*)
                (member-eq flag2 *flags*)
                )
           (equal (set-flag flag1 val1 (set-flag flag2 val2 x86))
                  (set-flag flag2 val2 (set-flag flag1 val1 x86))))
  :hints (("Goal" :use (:instance set-flag-of-set-flag-diff)
           :in-theory (disable set-flag-of-set-flag-diff)))
  :rule-classes nil)

;; todo: package
(defthm x86isa::idiv-spec-64-trim-arg1-axe-all
  (implies (axe-syntaxp (term-should-be-trimmed-axe '128 x 'acl2::all dag-array))
           (equal (idiv-spec-64 x y)
                  (idiv-spec-64 (trim 128 x) y)))
  :hints (("Goal" :in-theory (enable trim idiv-spec-64))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Only fires when x86 is not an IF/MYIF (to save time).
(defthm run-until-stack-shorter-than-base-axe
  (implies (and (axe-syntaxp (not (syntactic-call-of 'if x86 dag-array)))
                ;; (axe-syntaxp (not (syntactic-call-of 'myif x86 dag-array))) ; may be needed someday
                (stack-shorter-thanp old-rsp x86))
           (equal (run-until-stack-shorter-than old-rsp x86)
                  x86))
  :hints (("Goal" :in-theory (enable run-until-stack-shorter-than-base))))

;; Only fires when x86 is not an IF/MYIF (so we don't need IF lifting rules for x86-fetch-decode-execute and its subfunctions).
(defthm run-until-stack-shorter-than-opener-axe
  (implies (and (axe-syntaxp (not (syntactic-call-of 'if x86 dag-array)))
                ;; (axe-syntaxp (not (syntactic-call-of 'myif x86 dag-array))) ; may be needed someday
                (not (stack-shorter-thanp old-rsp x86)))
           (equal (run-until-stack-shorter-than old-rsp x86)
                  (run-until-stack-shorter-than old-rsp (x86-fetch-decode-execute x86))))
  :hints (("Goal" :in-theory (enable run-until-stack-shorter-than-opener))))

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

;; Only opens x86-fetch-decode-execute if we can resolve the (first byte of) the current instruction to a constant
;; Creates x86-fetch-decode-execute-base-new.
;; We tried just testing whether RIP is a constant, but sometimes RIP can be the variable TEXT-OFFSET.
;; Could simplify this for 64-bit mode (use rip and read) but then what about 32-bit mode?
;; ttodo: try using a binding hyp for proc-mode
(defopeners x86-fetch-decode-execute :suffix -new
  :hyps (;(poor-mans-quotep (rip x86))
         ;;(canonical-address-p (rip x86)) ; could drop, but this clarifies failures
         (canonical-address-p (let ((proc-mode (x86isa::x86-operation-mode x86)))
                                (x86isa::read-*ip proc-mode x86))) ; could drop, but this clarifies failures
         ;; ;; Requires us to be able to read the byte at the RIP:
         (poor-mans-quotep (let ((proc-mode (x86isa::x86-operation-mode x86)))
                             (mv-nth 1 (x86isa::rme08$inline proc-mode (x86isa::read-*ip proc-mode x86) 1 :x x86))))
         ;; (poor-mans-quotep (let ((proc-mode (x86isa::x86-operation-mode x86)))
         ;;                     (read 1 (x86isa::read-*ip proc-mode x86) x86)))
         ;; (poor-mans-quotep (read 1 (rip x86) x86))
         (not (ms x86))
         (not (fault x86))))

;; should be faster?
;; todo: continue specializing to 64-bit mode
(defthm x86-fetch-decode-execute-opener-safe-64
  (implies (and (canonical-address-p (x86isa::read-*ip 0 x86)) ; could drop, but this clarifies failures
                ;; ;; Requires us to be able to read the byte at the RIP:
                ;; todo: simplify this:
                (poor-mans-quotep (mv-nth 1 (x86isa::rme08$inline 0 (x86isa::read-*ip 0 x86) 1 :x x86)))
                ;; (poor-mans-quotep (let ((proc-mode (x86isa::x86-operation-mode x86)))
                ;;                     (read 1 (x86isa::read-*ip proc-mode x86) x86)))
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
                             (start-rip (x86isa::read-*ip proc-mode x86)))
                        (mv-let (flg acl2::|(THE (UNSIGNED-BYTE 52) PREFIXES)|
                                     acl2::|(THE (UNSIGNED-BYTE 8) REX-BYTE)|
                                     x86)
                          (get-prefixes proc-mode start-rip 0 0 15 x86)
                          (let* ((prefixes acl2::|(THE (UNSIGNED-BYTE 52) PREFIXES)|)
                                 (rex-byte acl2::|(THE (UNSIGNED-BYTE 8) REX-BYTE)|))
                            (if flg (!ms (let ((x86isa::erp nil))
                                           (cons (list ctx
                                                       :rip (rip x86)
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
                                                             :rip (rip x86)
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
                                                                      :rip (rip x86)
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
                                                                            :rip (rip x86)
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
                                                                                   :rip (rip x86)
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
                                                                                         :rip (rip x86)
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
                                                                                               :rip (rip x86)
                                                                                               :modr/m-byte-read-error flg)
                                                                                         x86isa::erp))
                                                                                 x86)
                                                                      (mv-let (flg temp-rip)
                                                                        (if x86isa::modr/m? (x86isa::add-to-*ip proc-mode temp-rip 1 x86)
                                                                          (mv nil temp-rip))
                                                                        (if flg (!ms (let ((x86isa::erp nil))
                                                                                       (cons (list ctx
                                                                                                   :rip (rip x86)
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
                                                                                                           :rip (rip x86)
                                                                                                           :sib-byte-read-error flg)
                                                                                                     x86isa::erp))
                                                                                             x86)
                                                                                  (mv-let (flg temp-rip)
                                                                                    (if x86isa::sib? (x86isa::add-to-*ip proc-mode temp-rip 1 x86)
                                                                                      (mv nil temp-rip))
                                                                                    (if flg (!ms (let ((x86isa::erp nil))
                                                                                                   (cons (list ctx
                                                                                                               :rip (rip x86)
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
                (integerp ad1)
                (unsigned-byte-p 48 n1)
                ;(integerp ad2)
                (unsigned-byte-p 48 n2))
           (equal (clear-extend n1 ad1 (write n2 ad2 val x86))
                  (clear-extend n1 ad1 (write n2 ad2 val (clear-extend n1 ad1 x86)))))
  :hints (("Goal" :in-theory (enable clear-extend))))

;; We've found the write to be cleared
(defthmd clear-extend-of-write-finish
  (implies (and ;(integerp ad)
                (unsigned-byte-p 48 n))
           (equal (clear-extend n ad (write n ad val x86))
                  (clear-retract n ad x86)))
  :hints (("Goal" :in-theory (enable clear-extend clear-retract))))

(defthmd clear-extend-of-write-of-clear-retract
  (implies (and (integerp ad1)
                (unsigned-byte-p 48 n1)
                ;(integerp ad2)
                (unsigned-byte-p 48 n2))
           (equal (clear-extend n1 ad1 (write n2 ad2 val (clear-retract n1 ad1 x86)))
                  (clear-retract n1 ad1 (write n2 ad2 val x86))))
  :hints (("Goal" :in-theory (enable clear-retract clear-extend))))

(defthmd write-of-clear-retract ; add -same to name
  (implies (and ;(integerp ad)
                (unsigned-byte-p 48 n))
           (equal (write n ad val (clear-retract n ad x86))
                  (write n ad val x86)))
  :hints (("Goal" :in-theory (enable clear-retract))))
