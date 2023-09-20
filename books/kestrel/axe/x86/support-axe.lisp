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
;(include-book "kestrel/x86/support" :dir :system)
(include-book "kestrel/x86/assumptions64" :dir :system) ;for ADDRESSES-OF-SUBSEQUENT-STACK-SLOTS-AUX
(include-book "kestrel/x86/assumptions32" :dir :system) ; for return-address-okp
(include-book "kestrel/x86/conditions" :dir :system) ; for jnl-condition
(include-book "kestrel/utilities/mv-nth" :dir :system)
(include-book "kestrel/axe/axe-syntax" :dir :system)
(include-book "kestrel/axe/axe-syntax-functions-bv" :dir :system)
(include-book "kestrel/axe/bv-rules-axe" :dir :system) ;for MYIF-BECOMES-BOOLIF-AXE and perhaps ACL2::BVNOT-TRIM-AXE-ALL (move myif-becomes-boolif?)
;(include-book "rule-lists")

;; Register a bunch of x86-related functions as known booleans:

;; mostly to suppress messages (but does this slow down anything?):
;; todo: have this print :redundant when it is
(acl2::add-known-boolean canonical-address-p$inline)
(acl2::add-known-boolean canonical-address-listp)
(acl2::add-known-boolean disjoint-p)
(acl2::add-known-boolean program-at)
(acl2::add-known-boolean x86p)
(acl2::add-known-boolean 64-bit-modep)
;(acl2::add-known-boolean addr-byte-alistp)
(acl2::add-known-boolean subset-p)
(acl2::add-known-boolean no-duplicates-p)
(acl2::add-known-boolean member-p)
(acl2::add-known-boolean separate)

(acl2::add-known-boolean separate)
(acl2::add-known-boolean x86p)
(acl2::add-known-boolean alignment-checking-enabled-p)

(acl2::add-known-boolean jnl-condition) ;todo: more

(acl2::add-known-boolean segment-is-32-bitsp)
(acl2::add-known-boolean well-formed-32-bit-segmentp)
(acl2::add-known-boolean code-segment-well-formedp)
(acl2::add-known-boolean code-segment-assumptions32-for-code)
(acl2::add-known-boolean eff-addrs-okp)
(acl2::add-known-boolean eff-addr-okp)
(acl2::add-known-boolean segments-separate)
(acl2::add-known-boolean acl2::bitp)
(acl2::add-known-boolean return-address-okp)

(defthmd part-install-width-low-becomes-bvcat-axe
  (implies (and (acl2::axe-bind-free (acl2::bind-bv-size-axe x 'xsize acl2::dag-array) '(xsize)) ;todo better message if we forget the package on dag-array (or make it a keyword?)
                (unsigned-byte-p xsize x)
                (natp xsize)              ;drop?
;                (< (+ width low) xsize)   ;allow = ?
                (natp low)
                (natp width))
           (equal (bitops::part-install-width-low val x width low)
                  (acl2::bvcat (max xsize (+ width low))
                               (acl2::slice (+ -1 xsize) (+ low width) x)
                               (+ width low)
                               (acl2::bvcat width val low x)))))

;todo: we could use unsigned-byte-p-forced in these rules...:

(defthmd ash-negative-becomes-slice-axe
  (implies (and (< n 0)
                (acl2::axe-bind-free (acl2::bind-bv-size-axe x 'xsize acl2::dag-array) '(xsize))
                (unsigned-byte-p xsize x)
         ;       (<= (- n) xsize)
                (integerp n))
           (equal (ash x n)
                  (acl2::slice (+ -1 xsize) (- n) x)))
  :hints (("Goal" :use (:instance acl2::ash-negative-becomes-slice (acl2::x x) (acl2::n n) (acl2::xsize xsize)))))

(defthmd logand-becomes-bvand-axe-arg1-axe
  (implies (and (acl2::axe-bind-free (acl2::bind-bv-size-axe x 'xsize acl2::dag-array) '(xsize))
                (unsigned-byte-p xsize x)
                (natp y))
           (equal (logand x y)
                  (acl2::bvand xsize x y)))
  :hints (("Goal" :use (:instance acl2::LOGAND-BECOMES-BVAND (size xsize) (acl2::y y))
           :in-theory (disable acl2::LOGAND-BECOMES-BVAND))))

(defthmd logand-becomes-bvand-axe-arg2-axe
  (implies (and (acl2::axe-bind-free (acl2::bind-bv-size-axe x 'xsize acl2::dag-array) '(xsize))
                (unsigned-byte-p xsize x)
                (natp y))
           (equal (logand y x)
                  (acl2::bvand xsize y x)))
  :hints (("Goal":use (:instance acl2::LOGAND-BECOMES-BVAND (size xsize) (acl2::y y))
           :in-theory (disable acl2::LOGAND-BECOMES-BVAND))))

(defthmd logior-becomes-bvor-axe
  (implies (and (acl2::axe-bind-free (acl2::bind-bv-size-axe x 'xsize acl2::dag-array) '(xsize))
                (acl2::axe-bind-free (acl2::bind-bv-size-axe y 'ysize acl2::dag-array) '(ysize))
                (unsigned-byte-p xsize x)
                (unsigned-byte-p ysize y))
           (equal (logior x y)
                  (acl2::bvor (max xsize ysize) x y)))
  :hints (("Goal" :in-theory (enable acl2::bvor))))

;todo: move
(defthm not-member-p-canonical-address-listp-when-disjoint-p-alt
  (implies (and (disjoint-p (create-canonical-address-list m addr) ;this hyp is commuted
                            (create-canonical-address-list n prog-addr))
                (member-p e (create-canonical-address-list m addr)))
           (equal (member-p e (create-canonical-address-list n prog-addr))
                  nil)))

(defthmd aref1-rewrite ;for axe
  (implies (and (not (equal :header n))
                (not (equal :default n))
                (assoc-equal n l))
           (equal (aref1 name l n)
                  (acl2::lookup-equal n l)))
  :hints (("Goal" :in-theory (e/d (acl2::lookup-equal aref1) ()))))

;We'll use aref1-rewrite to handle the aref1s.
;todo: use defopeners

(acl2::defopeners x86isa::64-bit-mode-two-byte-opcode-modr/m-p
                  :hyps ((syntaxp (quotep x86isa::opcode))
                         (unsigned-byte-p '8 x86isa::opcode))) ;todo: allow an unquoted 8 here

;why did this cause loops?
(defthm canonical-address-listp-of-cdr
  (implies (canonical-address-listp lst)
           (canonical-address-listp (cdr lst))))

;;(acl2::defopeners COMBINE-BYTES :hyps ((syntaxp (quotep x86isa::bytes))))

;;  Use def-constant-opener to enable Axe to evaluate ground calls of various
;;  functions:

(acl2::def-constant-opener logcount)
(acl2::def-constant-opener zip)
(acl2::def-constant-opener logcount)
(acl2::def-constant-opener separate)
(acl2::def-constant-opener nonnegative-integer-quotient)
(acl2::def-constant-opener evenp)

;; Flag-related functions (these seem safe to execute without tha requiring
;; more rules; for example, we expect jle-condition to always be called on flag
;; functions with the same arguments (dst and src), so either all the args to
;; jle-condition get evaluated or none of them do).

(acl2::def-constant-opener x86isa::zf-spec$inline)

(acl2::def-constant-opener x86isa::cf-spec8$inline)
(acl2::def-constant-opener x86isa::of-spec8$inline)
(acl2::def-constant-opener x86isa::pf-spec8$inline)
(acl2::def-constant-opener x86isa::sf-spec8$inline)
(acl2::def-constant-opener x86isa::adc-af-spec8$inline)
(acl2::def-constant-opener x86isa::add-af-spec8$inline)
(acl2::def-constant-opener x86isa::sub-af-spec8$inline)

(acl2::def-constant-opener x86isa::cf-spec16$inline)
(acl2::def-constant-opener x86isa::of-spec16$inline)
(acl2::def-constant-opener x86isa::pf-spec16$inline)
(acl2::def-constant-opener x86isa::sf-spec16$inline)
(acl2::def-constant-opener x86isa::adc-af-spec16$inline)
(acl2::def-constant-opener x86isa::add-af-spec16$inline)
(acl2::def-constant-opener x86isa::sub-af-spec16$inline)

(acl2::def-constant-opener x86isa::cf-spec32$inline)
(acl2::def-constant-opener x86isa::of-spec32$inline)
(acl2::def-constant-opener x86isa::pf-spec32$inline)
(acl2::def-constant-opener x86isa::sf-spec32$inline)
(acl2::def-constant-opener x86isa::adc-af-spec32$inline)
(acl2::def-constant-opener x86isa::add-af-spec32$inline)
(acl2::def-constant-opener x86isa::sub-af-spec32$inline)

(acl2::def-constant-opener x86isa::!rflagsbits->ac$inline)
(acl2::def-constant-opener x86isa::!rflagsbits->af$inline)
(acl2::def-constant-opener x86isa::!rflagsbits->cf$inline)
(acl2::def-constant-opener x86isa::!rflagsbits->of$inline)
(acl2::def-constant-opener x86isa::!rflagsbits->pf$inline)
(acl2::def-constant-opener x86isa::!rflagsbits->sf$inline)
(acl2::def-constant-opener x86isa::!rflagsbits->zf$inline)

(acl2::def-constant-opener x86isa::32-bit-mode-two-byte-opcode-modr/m-p)
(acl2::def-constant-opener x86isa::32-bit-compute-mandatory-prefix-for-two-byte-opcode$inline)

(acl2::def-constant-opener acl2::bool->bit$inline)

(acl2::def-constant-opener canonical-address-p$inline)

;(acl2::defopeners byte-ify :hyps ((syntaxp (and (quotep n) (quotep val)))))

(acl2::def-constant-opener byte-listp)

(acl2::defopeners acl2::get-symbol-entry-mach-o)

(acl2::defopeners acl2::get-all-sections-from-mach-o-load-commands)

(acl2::defopeners acl2::get-section-number-mach-o-aux)

(acl2::defopeners addresses-of-subsequent-stack-slots-aux)

(acl2::defopeners acl2::get-pe-section-aux)

(acl2::defopeners acl2::lookup-pe-symbol)

;; ;todo
;; (thm
;;  (equal (bitops::rotate-left-32 x places)
;;         (acl2::leftrotate32 places x))
;;  :hints (("Goal" :in-theory (enable bitops::rotate-left-32 ACL2::ROTATE-LEFT acl2::leftrotate32 acl2::leftrotate))))

(acl2::def-constant-opener bitops::rotate-left-32$inline)

(acl2::def-constant-opener acl2::rotate-left)

(defthm set-flag-of-set-flag-diff-axe
  (implies (and (syntaxp (and (quotep flag1)
                              (quotep flag2)
                              ))
                (axe-syntaxp (acl2::heavier-dag-term flag1 flag2))
                (not (equal flag1 flag2))
                (member-eq flag1 *flags*)
                (member-eq flag2 *flags*)
                )
           (equal (set-flag flag1 val1 (set-flag flag2 val2 x86))
                  (set-flag flag2 val2 (set-flag flag1 val1 x86))))
  :hints (("Goal" :use (:instance set-flag-of-set-flag-diff)
           :in-theory (disable set-flag-of-set-flag-diff)))
  :rule-classes nil)

(defthm x86isa::idiv-spec-64-trim-arg1-axe-all
  (implies (axe-syntaxp (acl2::term-should-be-trimmed-axe '128 acl2::x 'acl2::all acl2::dag-array))
           (equal (x86isa::idiv-spec-64 x y)
                  (x86isa::idiv-spec-64 (acl2::trim 128 acl2::x) y)))
  :hints (("Goal" :in-theory (e/d (acl2::trim x86isa::idiv-spec-64)
                                  nil))))
