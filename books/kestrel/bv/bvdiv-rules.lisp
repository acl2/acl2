; Rules about bvdiv
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "bvdiv")
(include-book "bvlt")
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))

;; 0 = x div y  becomes  x<y
(defthm equal-of-0-and-bvdiv
  (implies (natp size)
           (equal (equal 0 (bvdiv size x y))
                  (if (equal 0 (bvchop size y)) ;odd case
                      t
                    (bvlt size x y))))
  :hints (("Goal" :in-theory (enable bvdiv bvlt))))

;; 0 < x div y  becomes  x>=y
(defthm bvlt-of-0-and-bvdiv
  (implies (natp size)
           (equal (bvlt size 0 (bvdiv size x y))
                  (if (equal 0 (bvchop size y))
                      nil
                    (not (bvlt size x y)))))
  :hints (("Goal" :in-theory (enable bvdiv bvlt))))
