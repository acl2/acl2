; BV Library: additional logxor theorems
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "logxor")
(include-book "bvchop-def")
(include-book "logtail-def")
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
