; Rule about bvif together with other functions
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "bvif")
(include-book "bvlt")
(include-book "sbvlt")
(include-book "bvsx")
(include-book "bvmult")
(include-book "bvshl")
(local (include-book "bvplus"))

;let sizes differ?
(defthmd bvplus-of-bvif-arg2
  (equal (bvplus size (bvif size test y z) x)
         (bvif size test (bvplus size y x)
               (bvplus size z x)))
  :hints (("Goal" :in-theory (enable bvif))))

;let sizes differ?
(defthmd bvplus-of-bvif-arg3
  (equal (bvplus size x (bvif size test y z))
         (bvif size test (bvplus size x y)
               (bvplus size x z)))
  :hints (("Goal" :in-theory (enable bvif))))

;let sizes differ?
(defthm bvplus-of-bvif-arg3-safe
  (implies (syntaxp (and (quotep x)
                         (or (quotep y)
                             (quotep z))
                         (quotep size)))
           (equal (bvplus size x (bvif size test y z))
                  (bvif size test
                        ;; at least one of these two branches gets computed:
                        (bvplus size x y)
                        (bvplus size x z))))
  :hints (("Goal" :in-theory (enable bvif))))

;let sizes differ?
(defthm bvplus-of-bvif-arg2-safe
  (implies (syntaxp (and (quotep x)
                         (or (quotep y)
                             (quotep z))
                         (quotep size)))
           (equal (bvplus size (bvif size test y z) x)
                  (bvif size test
                        ;; at least one of these two branches gets computed:
                        (bvplus size y x)
                        (bvplus size z x))))
  :hints (("Goal" :in-theory (enable bvif))))

(defthm bvlt-of-bvif-arg2
  (equal (bvlt size (bvif size2 test a b) x)
         (boolif test
                 (bvlt size (bvchop size2 a) x)
                 (bvlt size (bvchop size2 b) x)))
  :hints (("Goal" :in-theory (enable bvif boolif))))

(defthm bvlt-of-bvif-arg2-safe
  (implies (and (syntaxp (and (quotep x)
                              (or (quotep a) (quotep b))
                              (quotep size)
                              (quotep size2))))
           (equal (bvlt size (bvif size2 test a b) x)
                  (boolif test
                          ;; at least one of these two branches gets computed:
                          (bvlt size (bvchop size2 a) x)
                          (bvlt size (bvchop size2 b) x))))
  :hints (("Goal" :in-theory (enable bvif boolif))))

;; not quite as safe
(defthm bvlt-of-bvif-arg2-safe2
  (implies (syntaxp (quotep x))
           (equal (bvlt size (bvif size2 test a b) x)
                  (boolif test
                          (bvlt size (bvchop size2 a) x)
                          (bvlt size (bvchop size2 b) x))))
  :hints (("Goal" :in-theory (enable bvif boolif))))

(defthm bvlt-of-bvif-arg3
  (equal (bvlt size x (bvif size2 test a b))
         (boolif test
                 (bvlt size x (bvchop size2 a))
                 (bvlt size x (bvchop size2 b))))
  :hints (("Goal" :in-theory (enable bvif boolif))))

(defthm bvlt-of-bvif-arg3-safe
  (implies (and (syntaxp (and (quotep x)
                              (or (quotep a) (quotep b))
                              (quotep size)
                              (quotep size2))))
           (equal (bvlt size x (bvif size2 test a b))
                  (boolif test
                          ;; at least one of these two branches gets computed:
                          (bvlt size x (bvchop size2 a))
                          (bvlt size x (bvchop size2 b)))))
  :hints (("Goal" :in-theory (enable bvif boolif))))

;; not quite as safe
(defthm bvlt-of-bvif-arg3-safe2
  (implies (syntaxp (quotep x))
           (equal (bvlt size x (bvif size2 test a b))
                  (boolif test
                          (bvlt size x (bvchop size2 a))
                          (bvlt size x (bvchop size2 b)))))
  :hints (("Goal" :in-theory (enable bvif boolif))))

;doesn't replicate any big terms
(defthm equal-of-bvif-safe
  (implies (syntaxp (and (quotep x)
                         ;;could drop this one?:
                         (or (quotep a)
                             (quotep b))
                         (quotep size)))
           (equal (equal x (bvif size test a b))
                  ;one of the branches here will be computed
                  (boolif test
                          (equal x (bvchop size a))
                          (equal x (bvchop size b)))))
    :hints (("Goal" :in-theory (enable bvif))))

(defthm sbvlt-of-bvif-when-sbvlt-arg3-alt
  (implies (and (sbvlt size x y)
                (posp size))
           (equal (sbvlt size x (bvif size test y z))
                  (if test
                      t
                    (sbvlt size x z)))))

(defthm sbvlt-of-bvif-when-sbvlt-arg4-alt
  (implies (and (sbvlt size x z)
                (posp size))
           (equal (sbvlt size x (bvif size test y z))
                  (if test
                      (sbvlt size x y)
                    t))))

(defthm sbvlt-of-bvif-when-not-sbvlt-arg3-alt
  (implies (and (not (sbvlt size x y))
                (posp size))
           (equal (sbvlt size x (bvif size test y z))
                  (if test
                      nil
                    (sbvlt size x z)))))

(defthm sbvlt-of-bvif-when-not-sbvlt-arg4-alt
  (implies (and (not (sbvlt size x z))
                (posp size))
           (equal (sbvlt size x (bvif size test y z))
                  (if test
                      (sbvlt size x y)
                    nil))))

(defthm sbvlt-of-bvif-when-sbvlt-arg3
  (implies (and (sbvlt size y x)
                (posp size))
           (equal (sbvlt size (bvif size test y z) x)
                  (if test
                      t
                    (sbvlt size z x)))))

(defthm sbvlt-of-bvif-when-sbvlt-arg4
  (implies (and (sbvlt size z x)
                (posp size))
           (equal (sbvlt size (bvif size test y z) x)
                  (if test
                      (sbvlt size y x)
                    t))))

(defthm sbvlt-of-bvif-when-not-sbvlt-arg3
  (implies (and (not (sbvlt size y x))
                (posp size))
           (equal (sbvlt size (bvif size test y z) x)
                  (if test
                      nil
                    (sbvlt size z x)))))

(defthm sbvlt-of-bvif-when-not-sbvlt-arg4
  (implies (and (not (sbvlt size z x))
                (posp size))
           (equal (sbvlt size (bvif size test y z) x)
                  (if test
                      (sbvlt size y x)
                    nil))))

;gen
(defthm bvsx-of-bvif
  (implies (and (natp new-size)
                (posp old-size))
           (equal (bvsx new-size old-size (bvif old-size test x y))
                  (bvif new-size
                        test
                        (bvsx new-size old-size x)
                        (bvsx new-size old-size y))))
  :hints (("Goal" :in-theory (enable bvif))))

(defthm bvsx-of-bvif-safe
  (implies (and (syntaxp (quotep new-size))
                (syntaxp (quotep old-size))
                (natp new-size)
                (posp old-size))
           (equal (bvsx new-size old-size (bvif old-size test x y))
                  (bvif new-size
                        test
                        (bvsx new-size old-size x)
                        (bvsx new-size old-size y))))
  :hints (("Goal" :in-theory (enable bvif))))

(defthm bvmult-of-bvif-arg3
  (implies (integerp size)
           (equal (bvmult size x (bvif size2 test y1 y2))
                  (bvif size
                        test
                        (bvmult size x (bvchop size2 y1))
                        (bvmult size x (bvchop size2 y2)))))
  :hints (("Goal" :in-theory (enable bvif))))

;todo: gen
;unsafe?
;to get stp to see the shift (bvshl gets rewritten with a constant shift amt?)
(defthm bvshl-of-bvif-arg3
  (equal (bvshl 32 x (bvif 5 test sa1 sa2))
         (bvif 32
               test
               (bvshl 32 x (bvchop 5 sa1))
               (bvshl 32 x (bvchop 5 sa2))))
  :hints (("Goal" :in-theory (enable bvif))))
