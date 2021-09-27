; BV Library: additional logand theorems
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This book contains theorems that mix LOGAND with BVCHOP and LOGTAIL.

(include-book "logand")
(include-book "bvchop-def")
(include-book "logtail-def")
(local (include-book "kestrel/arithmetic-light/expt2" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))

;; See also logmaskp.

;todo: make a version that matches a constant mask
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
