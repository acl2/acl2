; BV Library: rightrotate
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "bvcat-def")
(include-book "slice-def")
(include-book "../arithmetic-light/power-of-2p")
(include-book "../arithmetic-light/lg-def")
(local (include-book "../arithmetic-light/lg"))
(local (include-book "../arithmetic-light/mod"))
(local (include-book "../arithmetic-light/expt"))
(local (include-book "bvcat"))
(local (include-book "unsigned-byte-p"))

;; Rotate VAL to the right by AMT positions within a field of width WIDTH.  We
;; reduce the rotation amount modulo the width.
(defund rightrotate (width amt val)
  (declare (xargs :guard (and (natp width)
                              (natp amt)
                              (integerp val))
                  :split-types t)
           (type integer val amt)
           (type (integer 0 *) width))
  (if (= 0 width)
      0
    (let* ((amt (mod (ifix amt) width)))
      (bvcat amt
             (slice (+ -1 amt) 0 val)
             (- width amt)
             (slice (+ -1 width) amt val)))))

(defthm unsigned-byte-p-of-rightrotate-same
  (implies (natp size)
           (unsigned-byte-p size (rightrotate size x y)))
  :hints (("Goal" :in-theory (enable rightrotate natp))))

(defthm unsigned-byte-p-of-rightrotate
  (implies (and (<= size2 size1)
                (integerp size1)
                (natp size2))
           (unsigned-byte-p size1 (rightrotate size2 x y)))
  :hints (("Goal" :in-theory (enable rightrotate))))

(defthm rightrotate-of-0-arg1
  (equal (rightrotate 0 amt val)
         0)
  :hints (("Goal" :in-theory (enable rightrotate))))

(defthm rightrotate-of-0-arg2
  (equal (rightrotate width 0 val)
         (bvchop width val))
  :hints (("Goal" :in-theory (enable rightrotate))))

(defthm rightrotate-when-not-integerp-arg2
  (implies (not (integerp amt))
           (equal (rightrotate width amt val)
                  (rightrotate width 0 val)))
  :hints (("Goal" :in-theory (enable rightrotate))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund rightrotate16 (amt val)
  (declare (xargs :guard (and (natp amt)
                              (integerp val))
                  :split-types t)
           (type integer amt val))
  (rightrotate 16 amt val))

(defund rightrotate64 (amt val)
  (declare (xargs :guard (and (natp amt)
                              (integerp val))
                  :split-types t)
           (type integer amt val))
  (rightrotate 64 amt val))

(defthmd rightrotate-open-when-constant-shift-amount
  (implies (syntaxp (and (quotep amt)
                         (quotep width)))
           (equal (rightrotate width amt val)
                  (if (equal 0 width)
                      0
                    (let* ((amt (mod (ifix amt) width) ;(bvchop (integer-length (+ -1 width)) amt)
                                ))
                      (bvcat amt (slice (+ -1 amt) 0 val)
                             (- width amt)
                             (slice (+ -1 width) amt val))))))
  :hints (("Goal" :in-theory (enable rightrotate))))

(defthm rightrotate-of-mod-arg2
  (implies (and (natp width)
                (integerp amt))
           (equal (rightrotate width (mod amt width) val)
                  (rightrotate width amt val)))
  :hints (("Goal" :in-theory (enable rightrotate))))

(defthm rightrotate-of-bvchop-arg2-core
  (implies (and (power-of-2p width)
                ;(natp amt)
                )
           (equal (rightrotate width (bvchop (lg width) amt) x)
                  (rightrotate width amt x)))
  :hints (("Goal" :in-theory (enable rightrotate BVCHOP))))

(defthm rightrotate-of-bvchop-arg2
  (implies (and (syntaxp (and (quotep width)
                              (quotep size)))
                (equal size (lg width))
                (power-of-2p width)
                ;(natp amt)
                )
           (equal (rightrotate width (bvchop size amt) x)
                  (rightrotate width amt x)))
  :hints (("Goal" :in-theory (enable rightrotate BVCHOP))))

(defthm rightrotate-of-bvchop-arg3
  (implies (natp width)
           (equal (rightrotate width amt (bvchop width x))
                  (rightrotate width amt x)))
  :hints (("Goal" :in-theory (enable rightrotate))))

(defthm rightrotate-subst-arg2
  (implies (and (equal (bvchop size amt) k)
                (syntaxp (and (quotep k)
                              (not (quotep amt))))
                (equal size (lg width))
                (power-of-2p width))
           (equal (rightrotate width amt x)
                  (rightrotate width k x)))
  :hints (("Goal" :in-theory (enable rightrotate BVCHOP))))
