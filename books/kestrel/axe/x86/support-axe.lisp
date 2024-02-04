; Support for using Axe to reason about x86 code
;
; Copyright (C) 2016-2019 Kestrel Technology, LLC
; Copyright (C) 2020-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; This book contains supproting material that is Axe-specific (e.g., rules
;; that use axe-syntaxp or axe-bind-free).

;; TODO: Factor out any non-Axe-specific stuff

;; TODO: Make sure there are non-axe versions of all of these.

(include-book "kestrel/x86/bitops" :dir :system) ; needed for part-install-width-low-becomes-bvcat-axe
(include-book "kestrel/x86/assumptions64" :dir :system) ;for ADDRESSES-OF-SUBSEQUENT-STACK-SLOTS-AUX
(include-book "kestrel/x86/assumptions32" :dir :system) ; for return-address-okp
(include-book "kestrel/x86/conditions" :dir :system) ; for jnl-condition
(include-book "kestrel/x86/run-until-return" :dir :system)
(include-book "kestrel/axe/axe-syntax" :dir :system)
(include-book "kestrel/axe/known-booleans" :dir :system)
(include-book "kestrel/axe/axe-syntax-functions-bv" :dir :system)
(include-book "kestrel/axe/axe-syntax-functions" :dir :system)
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

(add-known-boolean bitp)
(add-known-boolean return-address-okp)

(defthmd part-install-width-low-becomes-bvcat-axe
  (implies (and (axe-bind-free (bind-bv-size-axe x 'xsize acl2::dag-array) '(xsize)) ;todo better message if we forget the package on dag-array (or make it a keyword?)
                (unsigned-byte-p xsize x)
                (natp xsize)              ;drop?
;                (< (+ width low) xsize)   ;allow = ?
                (natp low)
                (natp width))
           (equal (bitops::part-install-width-low val x width low)
                  (bvcat (max xsize (+ width low))
                               (slice (+ -1 xsize) (+ low width) x)
                               (+ width low)
                               (bvcat width val low x)))))

;todo: we could use unsigned-byte-p-forced in these rules...:

(defthmd ash-negative-becomes-slice-axe
  (implies (and (< n 0)
                (axe-bind-free (bind-bv-size-axe x 'xsize acl2::dag-array) '(xsize))
                (unsigned-byte-p xsize x)
         ;       (<= (- n) xsize)
                (integerp n))
           (equal (ash x n)
                  (slice (+ -1 xsize) (- n) x)))
  :hints (("Goal" :use (:instance acl2::ash-negative-becomes-slice (acl2::x x) (acl2::n n) (acl2::xsize xsize)))))

(defthmd logand-becomes-bvand-axe-arg1-axe
  (implies (and (axe-bind-free (bind-bv-size-axe x 'xsize acl2::dag-array) '(xsize))
                (unsigned-byte-p xsize x)
                (natp y))
           (equal (logand x y)
                  (bvand xsize x y)))
  :hints (("Goal" :use (:instance acl2::LOGAND-BECOMES-BVAND (size xsize) (acl2::y y))
           :in-theory (disable acl2::LOGAND-BECOMES-BVAND))))

(defthmd logand-becomes-bvand-axe-arg2-axe
  (implies (and (axe-bind-free (bind-bv-size-axe x 'xsize acl2::dag-array) '(xsize))
                (unsigned-byte-p xsize x)
                (natp y))
           (equal (logand y x)
                  (bvand xsize y x)))
  :hints (("Goal":use (:instance acl2::LOGAND-BECOMES-BVAND (size xsize) (acl2::y y))
           :in-theory (disable acl2::LOGAND-BECOMES-BVAND))))

;move this and similar stuff?
(defthmd logior-becomes-bvor-axe
  (implies (and (axe-bind-free (bind-bv-size-axe x 'xsize acl2::dag-array) '(xsize))
                (axe-bind-free (bind-bv-size-axe y 'ysize acl2::dag-array) '(ysize))
                (unsigned-byte-p xsize x)
                (unsigned-byte-p ysize y))
           (equal (logior x y)
                  (bvor (max xsize ysize) x y)))
  :hints (("Goal" :in-theory (enable bvor))))

;todo: move
(defthm not-member-p-canonical-address-listp-when-disjoint-p-alt
  (implies (and (disjoint-p (create-canonical-address-list m addr) ;this hyp is commuted
                            (create-canonical-address-list n prog-addr))
                (member-p e (create-canonical-address-list m addr)))
           (not (member-p e (create-canonical-address-list n prog-addr)))))

;We'll use aref1-rewrite to handle the aref1s.
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
(def-constant-opener zip)
(def-constant-opener logcount)
(def-constant-opener separate)
(def-constant-opener nonnegative-integer-quotient)
(def-constant-opener evenp)

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

(def-constant-opener x86isa::32-bit-mode-two-byte-opcode-modr/m-p)
(def-constant-opener x86isa::32-bit-compute-mandatory-prefix-for-two-byte-opcode$inline)

(def-constant-opener acl2::bool->bit$inline)

(def-constant-opener canonical-address-p$inline)

;(defopeners byte-ify :hyps ((syntaxp (and (quotep n) (quotep val)))))

(def-constant-opener byte-listp)

(defopeners acl2::get-symbol-entry-mach-o)
(defopeners acl2::get-all-sections-from-mach-o-load-commands)
(defopeners acl2::get-section-number-mach-o-aux)

(defopeners addresses-of-subsequent-stack-slots-aux)

(defopeners acl2::get-pe-section-aux)
(defopeners acl2::lookup-pe-symbol)

;; ;todo
;; (thm
;;  (equal (bitops::rotate-left-32 x places)
;;         (acl2::leftrotate32 places x))
;;  :hints (("Goal" :in-theory (enable bitops::rotate-left-32 ACL2::ROTATE-LEFT acl2::leftrotate32 acl2::leftrotate))))

(def-constant-opener bitops::rotate-left-32$inline)

(def-constant-opener acl2::rotate-left)

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

;; todo: packages on x
(defthm x86isa::idiv-spec-64-trim-arg1-axe-all
  (implies (axe-syntaxp (acl2::term-should-be-trimmed-axe '128 acl2::x 'acl2::all acl2::dag-array))
           (equal (x86isa::idiv-spec-64 x y)
                  (x86isa::idiv-spec-64 (acl2::trim 128 acl2::x) y)))
  :hints (("Goal" :in-theory (e/d (acl2::trim x86isa::idiv-spec-64)
                                  nil))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Only fires when x86 is not an IF/MYIF (to save time).
(defthm run-until-stack-shorter-than-base-axe
  (implies (and (axe-syntaxp (not (acl2::syntactic-call-of 'if x86 acl2::dag-array)))
                ;; (axe-syntaxp (not (syntactic-call-of 'myif x86 acl2::dag-array))) ; may be needed someday
                (stack-shorter-thanp old-rsp x86))
           (equal (run-until-stack-shorter-than old-rsp x86)
                  x86))
  :hints (("Goal" :in-theory (enable run-until-stack-shorter-than-base))))

;; Only fires when x86 is not an IF/MYIF (so we don't need IF lifting rules for x86-fetch-decode-execute and its subfunctions).
(defthm run-until-stack-shorter-than-opener-axe
  (implies (and (axe-syntaxp (not (acl2::syntactic-call-of 'if x86 acl2::dag-array)))
                ;; (axe-syntaxp (not (syntactic-call-of 'myif x86 acl2::dag-array))) ; may be needed someday
                (not (stack-shorter-thanp old-rsp x86)))
           (equal (run-until-stack-shorter-than old-rsp x86)
                  (run-until-stack-shorter-than old-rsp (x86-fetch-decode-execute x86))))
  :hints (("Goal" :in-theory (enable run-until-stack-shorter-than-opener))))

(def-constant-opener X86ISA::!EVEX-PREFIXES->BYTE0$INLINE)
(def-constant-opener X86ISA::!PREFIXES->REP$inline)
(def-constant-opener X86ISA::PREFIXES->REP$INLINE)
(def-constant-opener x86isa::!prefixes->seg$inline)

;; probably only needed for axe
(defthmd integerp-of-ctri
  (integerp (ctri acl2::i x86)))
