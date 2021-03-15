; Mixed theorems about bit-vector operations
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "sbvlt")
(include-book "bvlt")
(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))

(defthmd sbvlt-rewrite
  (implies (posp size)
           (equal (sbvlt size x y)
                  (if (equal 0 (getbit (+ -1 size) x))
                      (if (equal 0 (getbit (+ -1 size) y))
                          (bvlt (+ -1 size) x y)
                        nil)
                    (if (equal 0 (getbit (+ -1 size) y))
                        t
                      (bvlt (+ -1 size) x y)))))
  :hints (("Goal" :in-theory (e/d (sbvlt bvlt ;LOGEXT-BECOMES-BVCHOP-WHEN-POSITIVE
                                         logext-when-negative logext-when-positive logext-when-negative-2) (<-BECOMES-BVLT-ALT <-BECOMES-BVLT <-BECOMES-BVLT-free)))))
