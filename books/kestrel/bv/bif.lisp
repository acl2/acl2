; Single-bit IF
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "getbit")
(include-book "bitand")
(include-book "bitor")
(include-book "bvif")
(include-book "bool-to-bit")

;; single bit IF, where the test is a bit, not a boolean
;fixme do we use this?
(defund bif (test x y)
  (declare (xargs :guard (and (bitp test)
                              (bitp x)
                              (bitp y))))
  (if (equal test 0)
      (getbit 0 y)
    (getbit 0 x)))

(defthmd myif-becomes-bif
  (implies (and (booleanp test)
                (unsigned-byte-p 1 x)
                (unsigned-byte-p 1 y))
           (equal (myif test x y)
                  (bif (bool-to-bit test) x y)))
  :hints (("Goal" :in-theory (enable bif))))

 ;bozo gen the 1
(defthm unsigned-byte-p-of-bif
  (unsigned-byte-p 1 (bif test x y)))

(defthm bif-of-getbit-0
  (equal (bif test y (getbit 0 x))
         (bif test y x))
  :hints (("Goal" :in-theory (enable bif))))

(defthm bif-of-getbit-0-alt
  (equal (bif test (getbit 0 x) y)
         (bif test x y))
  :hints (("Goal" :in-theory (enable bif))))

(defthm bif-x-y-0
  (implies (and (unsigned-byte-p 1 x)
                (unsigned-byte-p 1 y))
           (equal (bif x y 0)
                  (bitand x y)))
  :hints (("Goal" :in-theory (enable bif))))

;; (defthm getbit-of-bif
;;   (implies (and (natp n))
;;            (equal (getbit n (bif test thenpart elsepart))
;;                   (bif test (getbit n thenpart) (getbit n elsepart))))
;;   :hints (("Goal" :in-theory (enable bvif myif))))

(defthmd bvif-1-equal-1
  (implies (unsigned-byte-p 1 x)
           (equal (bvif 1 (equal 1 x) tp ep)
                  (bif x (getbit 0 tp) (getbit 0 ep))))
  :hints (("Goal" :in-theory (enable bif))))

;rename bif to bitif?
(defthmd bif-rewrite
  (implies (unsigned-byte-p 1 test)
           (equal (bif test x y)
                  (bitor (bitand test x)
                         (bitand (bitnot test) y))))
  :hints (("Goal" :in-theory (enable bif))))

(defthm bvif-becomes-bif
  (equal (bvif 1 test x y)
         (bif (bool-to-bit test) x y))
  :hints (("Goal" :in-theory (enable bif bvif myif bool-to-bit))))
