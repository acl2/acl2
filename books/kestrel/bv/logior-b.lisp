; BV Library: additional logior theorems
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This book contains theorems that mix LOGIOR with BVCHOP and LOGTAIL.

(include-book "logior")
(include-book "bvchop-def")
(include-book "logtail-def")
(include-book "getbit-def")
(local (include-book "kestrel/arithmetic-light/expt2" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "logand")) ;;logior is defined in terms of logand
(local (include-book "lognot")) ;;logior is defined in terms of lognot
(local (include-book "getbit"))

(local (in-theory (disable logtail)))

(defthm logtail-of-logior
  (equal (logtail n (logior i j))
         (logior (logtail n i)
                 (logtail n j)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable logtail))))

(defthm bvchop-of-logior
  (equal (bvchop size (logior i j))
         (logior (bvchop size i)
                 (bvchop size j)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable bvchop))))

(defthm slice-of-logior
  (equal (slice high low (logior i j))
         (logior (slice high low i)
                 (slice high low j)))
  :hints (("Goal" :in-theory (enable slice))))

(defthm getbit-of-logior
  (equal (getbit n (logior i j))
         (logior (getbit n i)
                 (getbit n j)))
  :hints (("Goal" :in-theory (e/d (getbit)
                                  (bvchop-1-becomes-getbit)))))

(defthm logbitp-of-logior
  (implies (and (natp i)
                (integerp j1)
                (integerp j2))
           (equal (logbitp i (logior j1 j2))
                  (or (logbitp i j1) (logbitp i j2))))
  :hints (("Goal" :in-theory (enable logbitp-iff-getbit))))
