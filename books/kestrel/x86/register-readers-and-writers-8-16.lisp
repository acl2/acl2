; 8-bit and 16-bit register readers
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

(include-book "projects/x86isa/machine/state" :dir :system) ;for rgfi
(include-book "kestrel/bv/bvchop-def" :dir :system)
(include-book "kestrel/bv/slice-def" :dir :system)

;; These are provided as abbreviations only.  We will rewrite these to either
;; the 32-bit accessors (e.g., EAX) or the 64-bit accessors (e.g., RAX),
;; depending on the kind of executable being analyzed (32-bit or 64-bit).

;; 8-bit (low)
(defund al (x86) (declare (xargs :stobjs x86)) (bvchop 8 (rgfi *rax* x86)))
(defund bl (x86) (declare (xargs :stobjs x86)) (bvchop 8 (rgfi *rbx* x86)))
(defund cl (x86) (declare (xargs :stobjs x86)) (bvchop 8 (rgfi *rcx* x86)))
(defund dl (x86) (declare (xargs :stobjs x86)) (bvchop 8 (rgfi *rdx* x86)))
(defund sil (x86) (declare (xargs :stobjs x86)) (bvchop 8 (rgfi *rsi* x86)))
(defund dil (x86) (declare (xargs :stobjs x86)) (bvchop 8 (rgfi *rdi* x86)))
(defund spl (x86) (declare (xargs :stobjs x86)) (bvchop 8 (rgfi *rsp* x86)))
(defund bpl (x86) (declare (xargs :stobjs x86)) (bvchop 8 (rgfi *rbp* x86)))

;; 8-bit (high)
(defund ah (x86) (declare (xargs :stobjs x86)) (slice 15 8 (rgfi *rax* x86)))
(defund bh (x86) (declare (xargs :stobjs x86)) (slice 15 8 (rgfi *rbx* x86)))
(defund ch (x86) (declare (xargs :stobjs x86)) (slice 15 8 (rgfi *rcx* x86)))
(defund dh (x86) (declare (xargs :stobjs x86)) (slice 15 8 (rgfi *rdx* x86)))

;; 16-bit
(defund ax (x86) (declare (xargs :stobjs x86)) (bvchop 16 (rgfi *rax* x86)))
(defund bx (x86) (declare (xargs :stobjs x86)) (bvchop 16 (rgfi *rbx* x86)))
(defund cx (x86) (declare (xargs :stobjs x86)) (bvchop 16 (rgfi *rcx* x86)))
(defund dx (x86) (declare (xargs :stobjs x86)) (bvchop 16 (rgfi *rdx* x86)))
(defund si (x86) (declare (xargs :stobjs x86)) (bvchop 16 (rgfi *rsi* x86)))
(defund di (x86) (declare (xargs :stobjs x86)) (bvchop 16 (rgfi *rdi* x86)))
(defund sp (x86) (declare (xargs :stobjs x86)) (bvchop 16 (rgfi *rsp* x86)))
(defund bp (x86) (declare (xargs :stobjs x86)) (bvchop 16 (rgfi *rbp* x86)))
