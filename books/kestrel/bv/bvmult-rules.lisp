; Rules about bvmult
;
; Copyright (C) 2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "bvmult")
(include-book "bvlt")
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/arithmetic-light/divide" :dir :system))
(local (include-book "kestrel/arithmetic-light/times-and-divide" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))

;todo: combine with the other (and move and rename the other)
(defthmd bvmult-of-expt-gen
  (implies (and (< n size)
                (natp size)
                (natp n))
           (equal (bvmult size (expt 2 n) x)
                  (* (expt 2 n) (bvchop (- size n) x))))
  :hints (("Goal" :in-theory (enable bvmult))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
  (defthmd <-of-bvmult-arg1-core-1
    (implies (and (equal 0 (mod k2 k1))
                  ;;(< (* k1 (bvchop size x)) (expt 2 size)) ; the bvmult doesn't chop anything
                  (< (* k1 x) (expt 2 size)) ; the bvmult doesn't chop anything
                  (natp size)
                  (natp k1)
                  ;;(< 0 k1) ;;
                  (natp k2)
                  (natp x)
                  )
             (equal (< (bvmult size k1 x) k2)
                    (< (bvchop size x) (/ k2 k1))))
    :hints (("Goal" :cases ((<= 1 k1))
             :in-theory (enable bvmult UNSIGNED-BYTE-P)))))

(local
  (defthmd <-of-bvmult-arg1-core-2
    (implies (and (not (equal 0 (mod k2 k1)))
                  ;;(< (* k1 (bvchop size x)) (expt 2 size)) ; the bvmult doesn't chop anything
                  (< (* k1 x) (expt 2 size)) ; the bvmult doesn't chop anything
                  (natp size)
                  (natp k1)
                  (< 0 k1) ;;
                  (natp k2)
                  (natp x))
             (equal (< (bvmult size k1 x) k2)
                    (<= (bvchop size x) (/ k2 k1))))
    :hints (("Goal" :cases ((<= 1 k1))
             :in-theory (enable bvmult UNSIGNED-BYTE-P)))))

(defthmd <-of-bvmult-arg1-core
  (implies (and (< (* k1 x) (expt 2 size)) ; the bvmult doesn't chop anything
                ;;(< (* k1 (bvchop size x)) (expt 2 size)) ; the bvmult doesn't chop anything
                (natp size)
                (natp k1)
                (< 0 k1) ;;
                (natp k2)
                (natp x))
           (equal (< (bvmult size k1 x) k2)
                  (if (equal 0 (mod k2 k1))
                      (< (bvchop size x) (/ k2 k1))
                    (<= (bvchop size x) (/ k2 k1)))))
  :hints (("Goal" :in-theory (enable <-of-bvmult-arg1-core-1
                                     <-of-bvmult-arg1-core-2))))

;; todo: make a version where the constant is the second argument of the <
(defthm <-of-bvmult-of-constant-and-constant
  (implies (and (syntaxp (and (quotep k1) (quotep k2)))
                (natp x)
                (< (* k1 x) (expt 2 size)) ; the bvmult doesn't chop anything
                ;;(< (* k1 (bvchop size x)) (expt 2 size)) ; the bvmult doesn't chop anything
                (natp size)
                (posp k1); if k1=0, the whole bvmult is 0
                (natp k2))
           (equal (< (bvmult size k1 x) k2)
                  (if (equal 0 (mod k2 k1)) ; gets resolved
                      (< (bvchop size x) (/ k2 k1))
                    (<= (bvchop size x) (/ k2 k1)))))
  :hints (("Goal" :in-theory (enable <-of-bvmult-arg1-core))))

;todo: allow the sizes to differ
(defthm bvlt-of-constant-and-bvmult-of-constant-arg2
  (implies (and (syntaxp (and (quotep k1) (quotep k2)))
                (natp x)
                (< (* k1 x) (expt 2 size)) ; the bvmult doesn't chop anything
                ;;(< (* k1 (bvchop size x)) (expt 2 size)) ; the bvmult doesn't chop anything
                (natp size)
                (posp k1) ; if k1=0, the whole bvmult is 0
                (< k2 (expt 2 size))
                (natp k2))
           (equal (bvlt size (bvmult size k1 x) k2)
                  (if (equal 0 (mod k2 k1)) ; gets resolved
                      (bvlt size x (/ k2 k1))
                    (bvle size (bvchop size x) (floor k2 k1)))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable bvlt unsigned-byte-p <-of-bvmult-arg1-core))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd <-of-bvmult-arg2-core
  (implies (and ;;(< (* k1 (bvchop size x)) (expt 2 size)) ; the bvmult doesn't chop anything
             (< (* k1 x) (expt 2 size)) ; the bvmult doesn't chop anything
             (natp size)
             (posp k1) ; if k1=0, the whole bvmult is 0
             (natp k2)
             (natp x))
           (equal (< k2 (bvmult size k1 x))
                  (and (< (/ k2 k1) (bvchop size x))
                       (< k2 (expt 2 size)))))
  :hints (("Goal" :cases ((<= 1 k1))
           :in-theory (enable bvmult UNSIGNED-BYTE-P))))

(defthmd <-of-constant-and-bvmult-of-constant
  (implies (and (syntaxp (and (quotep k1) (quotep k2)))
                ;;(< (* k1 (bvchop size x)) (expt 2 size)) ; the bvmult doesn't chop anything
                (< (* k1 x) (expt 2 size)) ; the bvmult doesn't chop anything
                (natp size)
                (posp k1) ; if k1=0, the whole bvmult is 0
                (natp k2)
                (natp x))
           (equal (< k2 (bvmult size k1 x))
                  (and (< (/ k2 k1) ; gets computed
                          (bvchop size x))
                       (< k2 (expt 2 size)))))
  :hints (("Goal" :cases ((<= 1 k1))
           :in-theory (enable bvmult UNSIGNED-BYTE-P))))

;todo: allow the sizes to differ
(defthmd bvlt-of-constant-and-bvmult-of-constant
  (implies (and (syntaxp (and (quotep k1) (quotep k2)))
                ;;(< (* k1 (bvchop size x)) (expt 2 size)) ; the bvmult doesn't chop anything
                (< (* k1 x) (expt 2 size)) ; the bvmult doesn't chop anything
                (natp size)
                (posp k1) ; if k1=0, the whole bvmult is 0
                (natp k2)
                (natp x)
                (< k2 (expt 2 size)))
           (equal (bvlt size k2 (bvmult size k1 x))
                  (bvlt size
                        (floor k2 k1) ; gets computed
                        x)))
  :hints (("Goal" :in-theory (enable bvlt unsigned-byte-p <-of-bvmult-arg2-core))))
