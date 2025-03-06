; Redefinining functions from the x86isa model
;
; Copyright (C) 2016-2019 Kestrel Technology, LLC
; Copyright (C) 2020-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; This book redefines functions from the x86isa model in terms of our
;; functions, such as the BV functions.  Redefinitions that do not need any of
;; our functions should go into x86-changes.lisp.

(include-book "portcullis")
(include-book "projects/x86isa/machine/instructions/rotates-spec" :dir :system)
;(include-book "projects/x86isa/machine/get-prefixes" :dir :system)
;(include-book "flags")
;(include-book "kestrel/bv-lists/packbv" :dir :system)
;(include-book "kestrel/bv/bvshr" :dir :system)
(include-book "kestrel/bv/bvchop" :dir :system)
(include-book "kestrel/bv/getbit" :dir :system)
(include-book "kestrel/bv/bitxor" :dir :system)
;(include-book "kestrel/lists-light/finalcdr" :dir :system)
;(include-book "kestrel/lists-light/reverse-list" :dir :system)
(include-book "centaur/bitops/fast-rotate" :dir :system)
(include-book "kestrel/bv/rightrotate" :dir :system)
;(local (include-book "linear-memory"))
;(local (include-book "kestrel/bv/rules10" :dir :system)) ; todo, for floor-of-/-arg2
;(local (include-book "kestrel/bv/rules3" :dir :system)) ; todo, for logtail-of-one-more
;(local (include-book "kestrel/bv/logand-b" :dir :system))
;(local (include-book "kestrel/bv/logior-b" :dir :system))
(local (include-book "kestrel/bv/intro" :dir :system))
(local (include-book "kestrel/bv/logapp" :dir :system)) ; for loghead-becomes-bvchop, todo
(local (include-book "kestrel/bv/bitops" :dir :system))
(local (include-book "kestrel/bv/slice" :dir :system))
(local (include-book "kestrel/bv/bvcat" :dir :system))
(local (include-book "kestrel/bv/getbit" :dir :system))
(local (include-book "kestrel/bv/unsigned-byte-p-forced-rules" :dir :system))
;; (local (include-book "kestrel/arithmetic-light/limit-expt" :dir :system)) ;prevent calls of expt on huge args
;; (local (include-book "kestrel/arithmetic-light/expt2" :dir :system))
;; (local (include-book "kestrel/arithmetic-light/floor" :dir :system))
;; (local (include-book "kestrel/arithmetic-light/plus" :dir :system))
;; (local (include-book "kestrel/arithmetic-light/plus-and-minus" :dir :system))
;; (local (include-book "kestrel/arithmetic-light/minus" :dir :system))
;; (local (include-book "kestrel/library-wrappers/ihs-quotient-remainder-lemmas" :dir :system)) ;drop
;; (local (include-book "kestrel/lists-light/take" :dir :system))
;; (local (include-book "kestrel/lists-light/cons" :dir :system))
;; (local (include-book "kestrel/lists-light/append" :dir :system))
;; (local (include-book "kestrel/lists-light/nthcdr" :dir :system))
;; (local (include-book "kestrel/lists-light/len" :dir :system))
;; (local (include-book "kestrel/lists-light/nth" :dir :system))
;; (local (include-book "kestrel/library-wrappers/ihs-logops-lemmas" :dir :system)) ;todo

(in-theory (disable mv-nth))

;; TODO: Other sizes.
(defthm ror-spec-64-alt-def
  (equal (ror-spec-64 x n rflags)
         (let* ((n (bvchop 6 n))
                (result-value (rightrotate 64 n x)))
           (mv result-value
               ;; output flags:
               (if (equal n 0)
                   (bvchop 32 rflags)
                 (if (equal n 1)
                     ;; nicer than what the naive definition does?:
                     (!rflagsbits->cf
                       (getbit 0 x) ;(getbit 63 (rightrotate 64 1 x))
                       (!rflagsbits->of
                         ;; simplify?:
                         (bitxor (getbit 0 x) ; (getbit 63 (rightrotate 64 1 x))
                                 (getbit 63 x) ; (getbit 62 (rightrotate 64 1 x))
                                 )
                         rflags))
                   (!rflagsbits->cf (getbit 63 result-value) rflags)))
               ;; undefined flags:
               (if (equal n 1) 0 2048))))
  :hints (("Goal" :in-theory (e/d (acl2::logapp-becomes-bvcat-when-bv
                                   x86isa::ror-spec-64
                                   !rflagsbits->cf
                                   !rflagsbits->of
                                   rflagsbits
                                   x86isa::rflagsbits-fix
                                   bitops::rotate-right-64
                                   rflagsbits->af
                                   rflagsbits->df
                                   rflagsbits->zf
                                   rflagsbits->res5
                                   rflagsbits->vm
                                   rflagsbits->iopl
                                   rflagsbits->id
                                   rflagsbits->tf
                                   rflagsbits->res3
                                   rflagsbits->vif
                                   rflagsbits->nt
                                   rflagsbits->sf
                                   rflagsbits->ac
                                   rflagsbits->rf
                                   rflagsbits->pf
                                   rflagsbits->res4
                                   rflagsbits->vip
                                   rflagsbits->res2
                                   rflagsbits->intf
                                   rflagsbits->res1
                                   acl2::slice-becomes-getbit
                                   acl2::logtail-of-bvchop-becomes-slice
                                   acl2::rightrotate-open-when-constant-shift-amount)
                                  (;;ACL2::EQUAL-OF-CONS-AND-CONS
                                   ;;ACL2::EQUAL-OF-CONS
                                   ;;X86ISA::PART-SELECT-WIDTH-LOW-BECOMES-SLICE
                                   ;;ACL2::LOGAPP-EQUAL-REWRITE
                                   )))))
