; BV Library: additional logand theorems
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; todo: rename to logand-b.lisp

;; This book contains theorems that mix LOGAND with BVCHOP, LOGTAIL, etc.

(include-book "logand")
;(include-book "bvchop-def")
;(include-book "logtail-def")
(include-book "getbit-def")
(local (include-book "bvchop"))
(local (include-book "getbit"))
(local (include-book "kestrel/arithmetic-light/expt2" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))

;; See also logmaskp.

(defthm logand-with-mask-better
  (implies (natp size)
           (equal (logand (+ -1 (expt 2 size)) i)
                  (bvchop size i)))
  :hints (("Goal" :in-theory (enable bvchop))))

(defthm logand-with-mask-better-alt
  (implies (natp size)
           (equal (logand i (+ -1 (expt 2 size)))
                  (bvchop size i)))
  :hints (("Goal" :use (:instance logand-with-mask-better)
           :in-theory (disable logand-with-mask-better))))

;; todo: consider enabling
(defthmd logand-of-constant-becomes-bvchop-when-all-ones
  (implies (and (syntaxp (quotep k))
                (equal k (+ -1 (expt 2 (integer-length k)))))
           (equal (logand k i)
                  (bvchop (integer-length k) i))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm bvchop-of-logand
  (equal (bvchop size (logand i j))
         (logand (bvchop size i)
                 (bvchop size j)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (bvchop) (mod)))))

(defthm logtail-of-logand
  (equal (logtail n (logand i j))
         (logand (logtail n i)
                 (logtail n j)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable logtail))))

(defthm slice-of-logand
  (equal (slice high low (logand i j))
         (logand (slice high low i)
                 (slice high low j)))
  :hints (("Goal" :in-theory (enable slice))))

(defthm getbit-of-logand
  (equal (getbit n (logand i j))
         (logand (getbit n i)
                 (getbit n j)))
  :hints (("Goal" :in-theory (e/d (getbit)
                                  (bvchop-1-becomes-getbit
                                   )))))

(defthm logbitp-of-logand
  (implies (and (natp i)
                (integerp j1)
                (integerp j2))
           (equal (logbitp i (logand j1 j2))
                  (and (logbitp i j1) (logbitp i j2))))
  :hints (("Goal" :in-theory (enable logbitp-iff-getbit))))

(defthm logand-of-1-arg1
  (equal (logand 1 x)
         (getbit 0 x))
  :hints (("Goal" :in-theory (e/d (logand getbit bvchop)
                                  (bvchop-1-becomes-getbit)))))
