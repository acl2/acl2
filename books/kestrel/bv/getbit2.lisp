; More theorems about getbit
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "getbit")
(include-book "kestrel/utilities/polarity" :dir :system)

(defthm getbit-equal-1-polarity
  (implies (syntaxp (want-to-weaken (equal 1 (getbit n x))))
           (equal (equal 1 (getbit n x))
                  (not (equal 0 (getbit n x))))))

(defthm getbit-equal-1-polarity2
  (implies (syntaxp (want-to-weaken (equal (getbit n x) 1)))
           (equal (equal 1 (getbit n x))
                  (not (equal 0 (getbit n x))))))

(defthm getbit-equal-0-polarity
  (implies (syntaxp (want-to-weaken (equal 0 (getbit n x))))
           (equal (equal 0 (getbit n x))
                  (not (equal 1 (getbit n x))))))

(defthm getbit-equal-0-polarity2
  (implies (syntaxp (want-to-weaken (equal (getbit n x) 0)))
           (equal (equal 0 (getbit n x))
                  (not (equal 1 (getbit n x))))))

(defthmd equal-of-bvchop-when-equal-of-getbit-widen-polarity
  (implies (and (syntaxp (and (quotep k)
                              (quotep size)))
                (syntaxp (want-to-strengthen (equal (bvchop size x) k))) ;todo: why can't I put this in the syntaxp call above?
                (equal (getbit size x) k2)
                (syntaxp (quotep k2))
                (natp size))
           (equal (equal (bvchop size x) k)
                  (and (unsigned-byte-p size k) ;gets computed
                       (equal (bvchop (+ 1 size) x)
                              ;; gets computed
                              (+ (* k2 (expt 2 size))
                                 k)))))
  :hints (("Goal" :by equal-of-bvchop-when-equal-of-getbit-widen)))

(theory-invariant (incompatible (:rewrite BVCHOP-WHEN-TOP-BIT-NOT-1-FAKE-FREE)
                                (:rewrite equal-of-bvchop-when-equal-of-getbit-widen-polarity)))
