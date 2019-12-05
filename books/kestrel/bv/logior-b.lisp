; BV Library: additional logior theorems
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This book contains theorems that mix LOGIOR with BVCHOP and LOGTAIL.

(include-book "kestrel/bv/logior" :dir :system)
(include-book "kestrel/bv/bvchop-def" :dir :system)
(include-book "kestrel/bv/logtail-def" :dir :system)
(local (include-book "kestrel/arithmetic-light/expt2" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/bv/logand" :dir :system)) ;;logior is defined in terms of logand
(local (include-book "kestrel/bv/lognot" :dir :system)) ;;logior is defined in terms of lognot

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
