; 32-bit right rotate
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "rightrotate")
;(include-book "bvcat")
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "slice"))

(defund rightrotate32 (amt val)
  (declare (type integer amt val))
  (rightrotate 32 amt val))

;justifies the correctness of some operations performed by Axe
(defthm unsigned-byte-p-32-of-rightrotate32
  (unsigned-byte-p 32 (rightrotate32 amt val))
  :hints (("Goal" :in-theory (e/d (rightrotate32) (unsigned-byte-p)))))

(defthm unsigned-byte-p-of-rightrotate32
  (implies (and (<= 32 size)
                (integerp size))
           (unsigned-byte-p size (rightrotate32 x y)))
  :hints (("Goal" :in-theory (enable rightrotate32))))

;gen
(defthm rightrotate32-of-bvchop-32
  (equal (rightrotate32 amd (bvchop 32 x))
         (rightrotate32 amd x))
  :hints (("Goal" :in-theory (enable rightrotate32 RIGHTROTATE))))

(defthm rightrotate32-of-0
  (equal (rightrotate32 0 x)
         (bvchop 32 x))
  :hints (("Goal" :in-theory (enable rightrotate32))))

;todo: gen the 32
(defthmd bvcat-becomes-rightrotate
  (implies (and (equal mid+1 (+ 1 mid))
                (equal highsize (+ 1 mid))
                (equal lowsize (- 31 mid))
                (< mid 31)
                (natp mid))
           (equal (bvcat highsize
                         (slice mid 0 x)
                         lowsize
                         (slice 31 mid+1 x))
                  (acl2::rightrotate 32 (+ 1 mid) x)))
  :hints (("Goal" :in-theory (enable ACL2::RIGHTROTATE))))

;usual case (slice down to 0 has become bvchop)
(defthmd bvcat-becomes-rightrotate-2
  (implies (and (equal highsize size)
                (equal lowsize (- 32 size))
                (< size 31)
                (natp size))
           (equal (bvcat highsize
                         (bvchop size x) ;todo: won't the size here go away usually?
                         lowsize
                         (slice 31 size x))
                  (acl2::rightrotate 32 size x)))
  :hints (("Goal" :in-theory (e/d (ACL2::RIGHTROTATE) ()))))
