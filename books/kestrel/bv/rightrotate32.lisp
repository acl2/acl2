; 32-bit right rotate
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/bv/rightrotate" :dir :system)
;(include-book "kestrel/bv/bvcat" :dir :system)
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "slice"))

(defund rightrotate32 (amt val)
  (declare (type integer amt val))
  (rightrotate 32 amt val))

;gen
;justifies the correctness of some operations performed by Axe
(defthm unsigned-byte-p-of-rightrotate32
  (unsigned-byte-p 32 (rightrotate32 amt val))
  :hints (("Goal" :in-theory (e/d (rightrotate32) (unsigned-byte-p)))))

;gen
(defthm rightrotate32-of-bvchop-32
  (equal (rightrotate32 amd (bvchop 32 x))
         (rightrotate32 amd x))
  :hints (("Goal" :in-theory (enable rightrotate32 RIGHTROTATE))))

(defthm rightrotate32-of-0
  (equal (rightrotate32 0 x)
         (bvchop 32 x))
  :hints (("Goal" :in-theory (enable rightrotate32))))
