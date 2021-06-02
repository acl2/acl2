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

(defthmd bvdiv-of-bvdiv-arg2
  (implies (and (integerp y1)
                (integerp y2)
                (unsigned-byte-p size (* (bvchop size y1) (bvchop size y2))) ;gen?
                )
           (equal (bvdiv size (bvdiv size x y1) y2)
                  (bvdiv size
                         x
                         (* y1 y2)
                         )))
  :hints (("Goal" :in-theory (e/d (bvdiv
                                   bvchop-of-*-when-unsigned-byte-p-of-*-of-bvchop-and-bvchop)
                                  ( ;BVCHOP-IDENTITY
                                   ;;todo: clean these up:
                                   bvchop-times-cancel-better-alt
                                   bvchop-times-cancel-better
                                   bvchop-of-*-of-bvchop-arg2
                                   bvchop-of-*-of-bvchop)))))

;gen?
(defthm bvdiv-of-bvdiv-arg2-combine-constants
  (implies (and (syntaxp (and (quotep size)
                              (quotep y1)
                              (quotep y2)))
                ;; all get computed:
                (integerp y1)
                (integerp y2)
                (unsigned-byte-p size (* (bvchop size y1) (bvchop size y2))))
           (equal (bvdiv size (bvdiv size x y1) y2)
                  (bvdiv size
                         x
                         (* y1 y2) ;(bvchop size (* y1 y2))
                         )))
  :hints (("Goal" :in-theory (enable bvdiv-of-bvdiv-arg2))))

;todo: let the sizes differ
(defthm bvlt-of-bvdiv-constants
  (implies (and (syntaxp (and (quotep k1)
                              (quotep k2)
                              (quotep size)))
                (< 0 k1)
                (< 0 k2)
                (unsigned-byte-p size k1)
                (unsigned-byte-p size k2)
                (unsigned-byte-p size (* k1 k2)))
           (equal (bvlt size (bvdiv size x k1) k2)
                  (bvlt size x (* k1 k2))))
  :hints (("Goal" :in-theory (enable bvdiv bvlt)
           :use (:instance <-OF-FLOOR-OF-CONSTANT-AND-CONSTANT-GEN
                           (x (BVCHOP size X))
                           (k k2)
                           (k1 k1)))))
