; Rules about the rflags functions
;
; Copyright (C) 2016-2023 Kestrel Technology, LLC
; Copyright (C) 2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

(include-book "projects/x86isa/machine/rflags-spec" :dir :system)
(include-book "kestrel/x86/rflags-spec-sub" :dir :system)
(include-book "kestrel/bv/bvchop-def" :dir :system)
(local (include-book "kestrel/bv/bvchop" :dir :system))
(local (include-book "kestrel/bv/logext" :dir :system))
(local (include-book "kestrel/bv/slice" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))

(defthm bvchop-of-zf-spec
  (implies (posp size)
           (equal (bvchop size (zf-spec result))
                  (zf-spec result))))

(defthm logext-of-zf-spec
  (implies (and (< 1 size)
                (integerp size))
           (equal (logext size (zf-spec result))
                  (zf-spec result)))
  :hints (("Goal" :in-theory (enable zf-spec))))

;; Which of these do we want?:

(defthm of-spec-of-logext-32
  (equal (of-spec32 (logext 32 x))
         0)
  :hints (("Goal" :in-theory (enable of-spec32))))

(defthm sf-spec64-of-bvchop-64
  (equal (sf-spec64 (bvchop 64 x))
         (sf-spec64 x))
  :hints (("Goal" :in-theory (enable sf-spec64 acl2::logtail-of-bvchop))))

(defthm of-spec64-of-logext-64
  (equal (of-spec64 (logext 64 x))
         0)
  :hints (("Goal" :in-theory (enable of-spec64))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm bvchop-of-sub-zf-spec32
  (implies (and (<= 1 size)
                (integerp size))
           (equal (bvchop size (sub-zf-spec32 dst src))
                  (sub-zf-spec32 dst src)))
  :hints (("Goal" :in-theory (enable sub-zf-spec32))))

;; we open sub-zf-spec32 here, since it's not being passed to JXXX condition function:
;gen to any constant
(defthm equal-of-sub-zf-spec32-and-1
  (equal (equal (sub-zf-spec32 dst src) 1)
         (equal dst src))
  :hints (("Goal" :in-theory (enable sub-zf-spec32
                                     zf-spec
                                     acl2::bvchop-of-sum-cases))))

; commuted, only for axe
;gen to any constant
(defthmd equal-of-1-and-sub-zf-spec32
  (equal (equal 1 (sub-zf-spec32 dst src))
         (equal dst src)))
