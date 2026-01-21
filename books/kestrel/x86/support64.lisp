; Supporting material for 64-bit x86 Axe lifting
;
; Copyright (C) 2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; This book mixed x86isa notions with bv notions, so we put it in the X package.

(include-book "readers-and-writers64") ; for set-rip
;(include-book "kestrel/bv-lists/bv-array-read" :dir :system)
(include-book "kestrel/bv-lists/array-patterns" :dir :system) ; for bv-array-read-cases

;; todo: to be more general, support splitting when the bv-array-read is not the entire new rip term.
;; approach: create an identify function that causes things to be split (and ifs to be lifted)? and propagate it downward through a non-constant set-rip argument when there is something to split.
(defthm set-rip-of-bv-array-read-split-cases
  (implies (and (syntaxp (and (quotep data)
                              (quotep len)))
                (< len 20) ; todo: how many cases do we want to allow?
                ;; (unsigned-byte-p (ceiling-of-lg len) index)
                (bvle (ceiling-of-lg len) index (+ -1 len)) ; todo?
                (posp len)
                (natp index))
           (equal (set-rip (bv-array-read size len index data) x86)
                  ;; bv-array-read-cases here will then get unrolled:
                  (set-rip (bv-array-read-cases (+ -1 len) size len index data) x86)))
  :hints (("Goal" :in-theory (enable acl2::bv-array-read-becomes-bv-array-read-cases))))

(defthm set-rip-of-bvif-split
  (equal (set-rip (bvif size test tp ep) x86)
         (if test
             (set-rip (bvchop size tp) x86)
           (set-rip (bvchop size ep) x86))))
