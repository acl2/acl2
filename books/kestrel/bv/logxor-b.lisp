; BV Library: additional logxor theorems
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "logxor")
;(include-book "bvchop-def")
;(include-book "logtail-def")
(include-book "getbit-def")
(local (include-book "../arithmetic-light/plus"))
(local (include-book "../arithmetic-light/expt2"))
(local (include-book "../arithmetic-light/mod"))
(local (include-book "../arithmetic-light/times"))
(local (include-book "../arithmetic-light/floor"))
(local (include-book "lognot"))
(local (include-book "logeqv"))
(local (include-book "logior"))
(local (include-book "logand"))
(local (include-book "bvchop"))
(local (include-book "getbit"))

;; This book contains theorems that mix LOGXOR with BVCHOP and LOGTAIL.

(defthm bvchop-of-logxor
  (equal (bvchop size (logxor i j))
         (logxor (bvchop size i)
                 (bvchop size j)))
  :hints (("Goal" :in-theory (enable bvchop))))

;move
(defthm bvchop-of-lognot-of-bvchop
  (equal (bvchop n (lognot (bvchop n i)))
         (bvchop n (lognot i)))
  :hints (("Goal" :in-theory (enable lognot))))

;bozo FLOOR-MINUS-ERIC-BETTER looped on      (FLOOR '0 (EXPT '2 N))
(defthm logtail-of-logxor
  (equal (logtail n (logxor i j))
         (logxor (logtail n i)
                 (logtail n j)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable logtail))))

(defthm slice-of-logxor
  (equal (slice high low (logxor i j))
         (logxor (slice high low i)
                 (slice high low j)))
  :hints (("Goal" :in-theory (enable slice))))

(defthm getbit-of-logxor
  (equal (getbit n (logxor i j))
         (logxor (getbit n i)
                 (getbit n j)))
  :hints (("Goal" :in-theory (e/d (getbit)
                                  (bvchop-1-becomes-getbit)))))

(defthm logbitp-of-logxor
  (implies (and (natp i)
                (integerp j1)
                (integerp j2))
           (equal (logbitp i (logxor j1 j2))
                  (xor (logbitp i j1) (logbitp i j2))))
  :hints (("Goal" :in-theory (enable logbitp-iff-getbit))))
