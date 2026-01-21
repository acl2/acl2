; More supporting material for x86 reasoning
;
; Copyright (C) 2016-2019 Kestrel Technology, LLC
; Copyright (C) 2020-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;todo: move this material to libraries

(include-book "portcullis")
(include-book "projects/x86isa/machine/get-prefixes" :dir :system)
(include-book "flags")
;(include-book "support-x86") ;todo reduce
;(include-book "read-and-write") ; drop?
(include-book "kestrel/utilities/defopeners" :dir :system)
(include-book "kestrel/bv-lists/packbv" :dir :system)
(include-book "kestrel/bv/bvshr" :dir :system)
;(include-book "kestrel/lists-light/finalcdr" :dir :system)
;(include-book "kestrel/lists-light/reverse-list" :dir :system)
(include-book "centaur/bitops/fast-rotate" :dir :system)
(local (include-book "linear-memory"))
(local (include-book "kestrel/bv/rules10" :dir :system)) ; todo, for floor-of-/-arg2
(local (include-book "kestrel/bv/rules3" :dir :system)) ; todo, for logtail-of-one-more
(local (include-book "kestrel/bv/logand-b" :dir :system))
(local (include-book "kestrel/bv/logior-b" :dir :system))
(local (include-book "kestrel/arithmetic-light/limit-expt" :dir :system)) ;prevent calls of expt on huge args
(local (include-book "kestrel/arithmetic-light/expt2" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus-and-minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/minus" :dir :system))
(local (include-book "kestrel/library-wrappers/ihs-quotient-remainder-lemmas" :dir :system)) ;drop
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/lists-light/cons" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/library-wrappers/ihs-logops-lemmas" :dir :system)) ;todo

(local (in-theory (enable acl2::expt-becomes-expt-limited
                          acl2::car-becomes-nth-of-0)))

(local (in-theory (disable (:e expt)
                           ;; for speed:
                           ;ACL2::BVCHOP-IDENTITY
                           ;ACL2::UNSIGNED-BYTE-P-FROM-BOUNDS
                           )))

;; ;todo: it's an error to call this in app-view?
;; (defthm mv-nth-0-of-ia32e-la-to-pa-of-set-flag
;;   (implies (and ;(not (equal :ac flag))
;;             (app-view x86))
;;            (equal (mv-nth 0 (x86isa::ia32e-la-to-pa lin-addr r-w-x (set-flag flag val x86)))
;;                   (mv-nth 0 (x86isa::ia32e-la-to-pa lin-addr r-w-x x86))))
;;   :hints (("Goal" :in-theory (enable x86isa::ia32e-la-to-pa
;;                                      set-flag
;;                                      x86isa::rflagsbits->ac
;;                                      ))))

;; ;todo: it's an error to call this in app-view?
;; (defthm mv-nth-2-of-ia32e-la-to-pa-of-set-flag
;;   (implies (and ;(not (equal :ac flag))
;;             (app-view x86)
;;             (not (mv-nth 0 (x86isa::ia32e-la-to-pa lin-addr r-w-x (set-flag flag val x86)))))
;;            (equal (mv-nth 2 (x86isa::ia32e-la-to-pa lin-addr r-w-x (set-flag flag val x86)))
;;                   (set-flag flag val (mv-nth 2 (x86isa::ia32e-la-to-pa lin-addr r-w-x x86)))))
;;   :hints (("Goal" :in-theory (enable x86isa::ia32e-la-to-pa
;;                                      set-flag
;;                                      x86isa::rflagsbits->ac
;;                                      ))))

;; it's an error to call this in app-view?
;; (defthm app-view-of-mv-nth-2-of-ia32e-la-to-pa
;;   (implies (app-view x86)
;;            (app-view (mv-nth 2 (x86isa::ia32e-la-to-pa lin-addr r-w-x x86))))
;;   :hints (("Goal" :in-theory (enable x86isa::ia32e-la-to-pa))))

;; (defthm mv-nth-0-of-las-to-pas-of-set-flag
;;   (implies (and (app-view x86)
;; ;                (not (mv-nth 0 (x86isa::las-to-pas n lin-addr r-w-x x86)))
;;                 )
;;            (equal (mv-nth 0 (x86isa::las-to-pas n lin-addr r-w-x (set-flag flag val x86)))
;;                   (mv-nth 0 (x86isa::las-to-pas n lin-addr r-w-x x86))))
;;   :hints (("Goal" :in-theory (enable x86isa::las-to-pas ;set-flag
;;                                      ;app-view
;;                                      ))))

;; (defthm mv-nth-1-of-las-to-pas-of-set-flag
;;   (implies (app-view x86)
;;            (equal (mv-nth 1 (x86isa::las-to-pas n lin-addr r-w-x (set-flag flag val x86)))
;;                   (mv-nth 1 (x86isa::las-to-pas n lin-addr r-w-x x86))))
;;   :hints (("Goal" :in-theory (enable x86isa::las-to-pas ;set-flag
;;                                      ;app-view
;;                                      ))))

;; (thm
;;  (equal (mv-nth 1 (RB n addr r-x (set-flag flag val x86)))
;;         (mv-nth 1 (RB n addr r-x x86)))
;;  :hints (("Goal" :in-theory (enable rb))))



;;todo: need to get the standard 32-bit assumptions gathered up:

;; TODO: reads like this (READ 4 4214784 X86) should now be resolvable?

;(acl2::defopeners X86ISA::RME-SIZE$inline :hyps ((< X86ISA::EFF-ADDR '2000)))

;this case seems safe to handle:
; (SLICE '10 '7 (BVCAT '3 x '8 y))

;; (defthmd xw-of-set-flag
;;   (implies (not (equal x86isa::field :rflags))
;;            (equal (xw x86isa::field x86isa::index value (set-flag x86isa::flg x86isa::val x86))
;;                   (set-flag x86isa::flg x86isa::val
;;                             (xw x86isa::field x86isa::index value x86))))
;;   :hints (("Goal" :in-theory (acl2::e/d* (set-flag) (force (force))))))

;todo: why are cons nests arising during rewriting?



;; no loop stopper
;; (defthm set-flag-set-flag-different-concrete-indices-better
;;   (implies (and (syntaxp (quotep i1))
;;                 (syntaxp (quotep i2))
;;                 (< i1 i2) ;gets computed
;;                 (member i1 *flg-names*)
;;                 (member i2 *flg-names*)
;;                 (x86p x86))
;;            (equal (set-flag i2 v2 (set-flag i1 v1 x86))
;;                   (set-flag i1 v1 (set-flag i2 v2 x86)))))

;; (thm
;;  (implies (zp amt)
;;           (equal (bvshr 32 x amt)
;;                  (bvchop 32 x)))
;;  :hints (("Goal" :in-theory (enable bvshr zp))))



;move
(defthm slice-of-minus-of-expt-same-as-low
  (implies (and (natp k)
                (natp high))
           (equal (slice high k (- (expt 2 k)))
                  (if (<= k high)
                      (+ -1 (expt 2 (- (+ 1 high) k)))
                    0)))
  :hints (("Goal" :in-theory (enable acl2::slice-of-minus))))

(defthm floor-lemma
  (IMPLIES (AND (< N 0)
                (NATP LOW)
                (INTEGERP HIGH)
                (<= LOW HIGH)
                (INTEGERP N)
                (INTEGERP X))
           (EQUAL (FLOOR X (* (EXPT 2 LOW) (/ (EXPT 2 N))))
                  (FLOOR (* X (EXPT 2 N)) (EXPT 2 LOW)))))

;todo: figure out how to print the hits but not the result of the rewrite

;; ;; what a mess is bitops::rotate-left-32.
;; (thm
;;  (implies (and (natp x)
;;                (natp places)
;;                (< places 32))
;;           (equal (bitops::rotate-left-32 x places)
;;                  (acl2::leftrotate 32 places x)))
;;  :hints (("Goal" :in-theory (e/d (acl2::rotate-left
;;                                   acl2::leftrotate
;;                                   ;;repeatbit
;;                                   )
;;                                  (ACL2::EXPONENTS-ADD)))))

;; Sections:
;; Idx Name          Size      VMA       LMA       File off  Algn
;;   0 UPX0          00004000  00401000  00401000  00000400  2**2
;;                   CONTENTS, ALLOC, CODE
;;   1 UPX1          00000a00  00405000  00405000  00000400  2**2
;;                   CONTENTS, ALLOC, LOAD, CODE, DATA
;;   2 UPX2          00000200  00406000  00406000  00000e00  2**2
;;                   CONTENTS, ALLOC, LOAD, DATA

;; It's trying to read from #x40445C.  Add assumption (equal 0 (read #x4000 #x401000 x86)).
;; Now it's reading from #x405A00, which is after the end of the UPX1 section but before UPX2. Add assumption (equal 0 (read #x600 #x405a00 x86)).
;; Now it's reading from #x406200, which is after the UPX2 section.  Should we try assuming those bytes are 0 as well?

;; it's an error to call this in app-view?
;; (defthm mv-nth-0-of-las-to-pas-of-set-flag
;;   (implies (app-view x86)
;;            (equal (mv-nth 0 (x86isa::las-to-pas n lin-addr r-w-x (set-flag flag val x86)))
;;                   (mv-nth 0 (x86isa::las-to-pas n lin-addr r-w-x x86))))
;;   :hints (("Goal" :in-theory (enable x86isa::las-to-pas x86isa::ia32e-la-to-pa))))

;; could move some of this stuff to linear-memory.lisp:

(defthm mv-nth-0-of-rb-1-of-set-flag
  (equal (mv-nth 0 (rb-1 n addr r-x (set-flag flag val x86)))
         (mv-nth 0 (rb-1 n addr r-x x86)))
  :hints (("Goal" :in-theory (enable rb-1))))

(defthm mv-nth-0-of-rb-1-of-set-flag
  (equal (mv-nth 0 (rb-1 n addr r-x (set-flag flag val x86)))
         (mv-nth 0 (rb-1 n addr r-x x86)))
  :hints (("Goal" :in-theory (enable rb-1))))

(defthm mv-nth-0-of-rvm08-of-set-flag
  (equal (mv-nth 0 (rvm08 addr (set-flag flag val x86)))
         (mv-nth 0 (rvm08 addr x86)))
  :hints (("Goal" :in-theory (enable rvm08))))

(defthm mv-nth-1-of-rvm08-of-set-flag
  (equal (mv-nth 1 (rvm08 addr (set-flag flag val x86)))
         (mv-nth 1 (rvm08 addr x86)))
  :hints (("Goal" :in-theory (enable rvm08))))

(defthm mv-nth-1-of-rb-1-of-set-flag
  (implies (app-view x86)
           (equal (mv-nth 1 (rb-1 n addr r-x (set-flag flag val x86)))
                  (mv-nth 1 (rb-1 n addr r-x x86))))
  :hints (("Goal" :in-theory (enable rb-1))))

(defthm mv-nth-0-of-rme08-of-set-flag
  (implies (app-view x86)
           (equal (mv-nth 0 (x86isa::rme08 proc-mode eff-addr seg-reg rx (set-flag flag val x86)))
                  (mv-nth 0 (x86isa::rme08 proc-mode eff-addr seg-reg rx x86))))
  :hints (("Goal" :in-theory (enable set-flag x86isa::rme08 rb))))

(defthm mv-nth-1-of-rme08-of-set-flag
  (implies (app-view x86)
           (equal (mv-nth 1 (x86isa::rme08 proc-mode eff-addr seg-reg rx (set-flag flag val x86)))
                  (mv-nth 1 (x86isa::rme08 proc-mode eff-addr seg-reg rx x86))))
  :hints (("Goal" :in-theory (enable set-flag x86isa::rme08 rb))))

;; (defthm mv-nth-0-of-get-prefixes-of-set-flag
;;   (implies (app-view x86)
;;            (equal (mv-nth 0 (get-prefixes proc-mode start-rip prefixes rex-byte cnt (set-flag flag val x86)))
;;                   (mv-nth 0 (get-prefixes proc-mode start-rip prefixes rex-byte cnt x86))))
;;   :hints (("Goal" :expand (:free (proc-mode)
;;                                  (get-prefixes proc-mode start-rip
;;                                                prefixes rex-byte cnt (set-flag flag val x86)))
;;            :induct (get-prefixes proc-mode start-rip prefixes rex-byte cnt x86)
;;            :in-theory (enable get-prefixes x86isa::add-to-*ip))))

;; (defthm mv-nth-1-of-get-prefixes-of-set-flag
;;   (implies (app-view x86)
;;            (equal (mv-nth 1 (get-prefixes proc-mode start-rip prefixes rex-byte cnt (set-flag flag val x86)))
;;                   (mv-nth 1 (get-prefixes proc-mode start-rip prefixes rex-byte cnt x86))))
;;   :hints (("Goal" :expand (:free (proc-mode) (get-prefixes proc-mode start-rip
;;                                         prefixes rex-byte cnt (set-flag flag val x86)))
;;            :induct (get-prefixes proc-mode start-rip prefixes rex-byte cnt x86)
;;            :in-theory (enable get-prefixes x86isa::add-to-*ip))))

(in-theory (disable butlast))

(local (in-theory (disable ACL2::CAR-BECOMES-NTH-OF-0))) ;todo

;; (DEFUN WRITE-2-addr-induct (N BASE-ADDR addr2 VAL X86)
;;   (declare (xargs :stobjs x86
;;                   :verify-guards nil)
;;            (irrelevant addr2))
;;   (IF (ZP N)
;;       x86
;;       (LET ((X86 (!MEMI (BVCHOP 48 BASE-ADDR)
;;                         (BVCHOP 8 VAL)
;;                         X86)))
;;            (WRITE-2-addr-induct (+ -1 N)
;;                                 (+ 1 BASE-ADDR)
;;                                 (+ 1 addr2)
;;                                 (LOGTAIL 8 VAL)
;;                                 X86))))


;; (thm
;;  (implies (and ;(< addr1 281474976710655)
;;                (< addr1 n)
;;                (unsigned-byte-p 48 addr1)
;;                (<= n 281474976710656)
;; ;(not (zp n))
;;                (natp n)
;;                )
;;           (equal (memi addr1 (write n 0 val x86))
;;                  (slice (+ 7 (* 8 addr1))
;;                         (* 8 addr1)
;;                         val))))

(acl2::defopeners REVAPPEND) ;drop?
