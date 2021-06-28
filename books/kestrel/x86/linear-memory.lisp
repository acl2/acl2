; Rules about memory
;
; Copyright (C) 2016-2019 Kestrel Technology, LLC
; Copyright (C) 2020-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X86ISA") ;; unlike most books, this one is in the X86ISA package

;; Some theorems about linear memory operations in the x86 model, including RB,
;; RB-1, RML-size, and RML-<xx> where <xx> is 08/16/32/48/64/80/128.

(include-book "projects/x86isa/machine/linear-memory" :dir :system)
(local (include-book "kestrel/bv/unsigned-byte-p" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))

(in-theory (disable rb rb-1 rml-size))

;move
(defthm unsigned-byte-p-of-0
  (equal (unsigned-byte-p size 0)
         (natp size))
  :hints (("Goal" :in-theory (enable unsigned-byte-p))))

(defthm mv-nth-0-of-rb-1-of-xw
  (implies (not (equal :mem fld))
           (equal (mv-nth 0 (rb-1 n addr r-x (xw fld index val x86)))
                  (mv-nth 0 (rb-1 n addr r-x x86))))
  :hints (("Goal" :in-theory (e/d (rb-1) (x86p-xw)))))

(defthm mv-nth-0-of-rb-of-xw-when-app-view
  (implies (and (not (equal fld :mem))
                (not (equal fld :app-view))
                (app-view x86))
           (equal (mv-nth 0 (rb n addr r-x (xw fld index val x86)))
                  (mv-nth 0 (rb n addr r-x x86))))
  :hints (("Goal" :in-theory (e/d (rb) (rb-1)))))

(defthm mv-nth-0-of-rml-size-of-xw-when-app-view
  (implies (and (not (equal fld :mem))
                (not (equal fld :app-view))
                (app-view x86))
           (equal (mv-nth 0 (rml-size nbytes addr r-x (xw fld index val x86)))
                  (mv-nth 0 (rml-size nbytes addr r-x x86))))
  :hints (("Goal" :in-theory (e/d (rml-size
                                   rml16
                                   rml32
                                   rml48
                                   rml64
                                   rml80
                                   rml128)
                                  ()))))

;TODO: The r-x param of rb-1 is irrelevant (drop it?)
;; This clearly shows that the param is irrelevant, but this would loop as a rewrite rule.
(defthm rb-1-rx-irrel
  (equal (rb-1 n addr r-x     x86)
         (rb-1 n addr r-x-alt x86))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable rb-1))))

;; Take advance of the fact that the r-w-x param is irrelevant to normalize it.
(defthm rb-1-when-not-r
  (implies (not (eq :r r-x))
           (equal (rb-1 n addr r-x x86)
                  (rb-1 n addr :r x86)))
  :hints (("Goal" :in-theory (enable rb-1))))

;avoids all the special cases in rml-size
(defthm rml-size-becomes-rb
  (implies (and (app-view x86)
                (canonical-address-p addr)
                (canonical-address-p (+ -1 addr nbytes)))
           (equal (rml-size nbytes addr r-x x86)
                  (rb nbytes addr r-x x86)))
  :hints (("Goal" :in-theory (enable rml-size
                                     rml08
                                     rml16
                                     rml32
                                     rml48
                                     rml64
                                     rml80
                                     rml128))))

(defthm mv-nth-1-of-rml-size-of-0
  (equal (mv-nth 1 (rml-size 0 addr r-x x86))
         0)
  :hints (("Goal" :in-theory (enable rml-size))))

;; Take advance of the fact that the r-w-x param is irrelevant to normalize it.
(defthm mv-nth-1-of-rb-1-when-not-natp-cheap
  (implies (not (natp n))
           (equal (mv-nth 1 (rb-1 n addr r-x x86))
                  0))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable rb-1))))

; better than x86isa::size-of-rb-1
(defthm unsigned-byte-p-of-mv-nth-1-of-rb-1
  (implies (and (<= (* 8 n) m)
                (natp m)
                (x86p x86))
           (unsigned-byte-p m (mv-nth 1 (rb-1 n addr r-x x86))))
  :hints (("Goal" :use (:instance size-of-rb-1 (m (* 8 n)))
           :in-theory (e/d (ash ifix)
                           (size-of-rb-1)))))

(defthm mv-nth-2-of-rb-1-when-app-view
  (implies (app-view x86)
           (equal (mv-nth 2 (rb-1 n addr r-x x86))
                  x86))
  :hints (("Goal" :in-theory (enable rb-1))))

(defthm mv-nth-2-of-rb-when-app-view
  (implies (app-view x86)
           (equal (mv-nth 2 (rb n addr r-x x86))
                  x86))
  :hints (("Goal" :in-theory (enable rb))))

(defthm mv-nth-2-of-rml08-when-app-view
  (implies (app-view x86)
           (equal (mv-nth 2 (rml08 addr r-x x86))
                  x86))
  :hints (("Goal" :in-theory (enable rml08))))

(defthm mv-nth-2-of-rml16-when-app-view
  (implies (app-view x86)
           (equal (mv-nth 2 (rml16 addr r-x x86))
                  x86))
  :hints (("Goal" :in-theory (enable rml16))))

(defthm mv-nth-2-of-rml32-when-app-view
  (implies (app-view x86)
           (equal (mv-nth 2 (rml32 addr r-x x86))
                  x86))
  :hints (("Goal" :in-theory (enable rml32))))

(defthm mv-nth-2-of-rml48-when-app-view
  (implies (app-view x86)
           (equal (mv-nth 2 (rml48 addr r-x x86))
                  x86))
  :hints (("Goal" :in-theory (enable rml48))))

(defthm mv-nth-2-of-rml64-when-app-view
  (implies (app-view x86)
           (equal (mv-nth 2 (rml64 addr r-x x86))
                  x86))
  :hints (("Goal" :in-theory (enable rml64))))

(defthm mv-nth-2-of-rml80-when-app-view
  (implies (app-view x86)
           (equal (mv-nth 2 (rml80 addr r-x x86))
                  x86))
  :hints (("Goal" :in-theory (enable rml80))))

(defthm mv-nth-2-of-rml128-when-app-view
  (implies (app-view x86)
           (equal (mv-nth 2 (rml128 addr r-x x86))
                  x86))
  :hints (("Goal" :in-theory (enable rml128))))

(defthm mv-nth-2-of-rml-size-when-app-view
  (implies (app-view x86)
           (equal (mv-nth 2 (rml-size nbytes addr r-x x86))
                  x86))
  :hints (("Goal" :in-theory (enable rml-size))))
