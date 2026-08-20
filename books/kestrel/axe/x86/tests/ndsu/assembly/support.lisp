; Support for the books in this subtree
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; The main goal of this book is to spare each book in this subtree from
;; including kestrel/axe/x86/unroller, which is quite slow to include.

;; A replacement for the unroller book that is much faster to include:
(include-book "kestrel/axe/x86/unroller-code-only" :dir :system)

;; We also (currently) need the following, to get all the proofs in this
;; subtree to go through.  Not all books in this subtree need all of these, so
;; we could move just the necessary ones to each book.

(include-book "kestrel/bv/bvand" :dir :system)
(include-book "kestrel/bv/bvor" :dir :system)
(include-book "kestrel/bv/bvxor" :dir :system)
(include-book "kestrel/bv/bvplus" :dir :system)
(include-book "kestrel/bv/bvminus" :dir :system)
(include-book "kestrel/bv/getbit" :dir :system)
(include-book "kestrel/bv/bvchop" :dir :system)
(include-book "kestrel/bv/trim-intro-rules" :dir :system)
(include-book "kestrel/bv/trim-elim-rules-bv" :dir :system)
(include-book "kestrel/bv/bvlt" :dir :system) ; drop?
(include-book "kestrel/bv/bvcount" :dir :system)
(include-book "kestrel/bv/bitops" :dir :system) ; for ACL2::PART-SELECT-WIDTH-LOW-BECOMES-SLICE-GEN -- or build that into the lifter
;; todo: reduce this?:
(include-book "kestrel/x86/read-and-write" :dir :system)

(in-theory (e/d (x::cf-spec8-becomes-getbit ; todo: gather these into Axe rule-lists
                 x::cf-spec16-becomes-getbit
                 x::cf-spec32-becomes-getbit
                 x::cf-spec64-becomes-getbit
                 x::sf-spec8-becomes-getbit
                 x::sf-spec16-becomes-getbit
                 x::sf-spec32-becomes-getbit
                 x::sf-spec64-becomes-getbit
                 x86isa::zf-spec$inline
                 x86isa::sub-cf-spec8-opener ; todo: package on these
                 x86isa::sub-cf-spec16-opener
                 x86isa::sub-cf-spec32-opener
                 x86isa::sub-cf-spec64-opener
                 x::add-af-spec8-becomes-bvlt
                 x::add-af-spec16-becomes-bvlt
                 x::add-af-spec32-becomes-bvlt
                 x::add-af-spec64-becomes-bvlt
                 x::adc-af-spec8-becomes-bvlt
                 x::adc-af-spec16-becomes-bvlt
                 x::adc-af-spec32-becomes-bvlt
                 x::adc-af-spec64-becomes-bvlt
                 x::sub-af-spec8-becomes-bvlt
                 x::sub-af-spec16-becomes-bvlt
                 x::sub-af-spec32-becomes-bvlt
                 x::sub-af-spec64-becomes-bvlt
                 x::sbb-af-spec8-becomes-bvlt
                 x::sbb-af-spec16-becomes-bvlt
                 x::sbb-af-spec32-becomes-bvlt
                 x::sbb-af-spec64-becomes-bvlt
                 slice-becomes-getbit
                 x::read-of-+-arg2)
                ;;todo:
                (x::read-of-bvplus
                 x::read-of-bvplus-normalize
                 x::bvcat-of-read-and-read-combine ; loops with the blasting rules
                 acl2::unsigned-byte-p-of-+-of-constant-strong ; turns unsigned-byte-p claims into < claims
                 )))

(make-event `(in-theory (enable ,@(x::register-aliases64)
                                ,@(x::bitops-to-bv-rules))))
