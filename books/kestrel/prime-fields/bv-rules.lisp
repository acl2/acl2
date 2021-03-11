; Prime field and BV rules
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PFIELD")

;; This book mixes prime-fields and BV operations.

(include-book "prime-fields")
(include-book "../bv/bvnot")
(include-book "../bv/bvchop")
(include-book "../bv/bvxor")
(include-book "../bv/bitxor")
(include-book "../bv/bvcat")
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus-and-minus" :dir :system))

(defthm fep-of-bvchop
  (implies (and (< (expt 2 size) p)
                (integerp p))
           (fep (acl2::bvchop size x)
                p))
  :hints (("Goal" :in-theory (enable fep))))

(defthm fep-of-bvxor
  (implies (and (< (expt 2 size) p)
                (integerp p))
           (fep (acl2::bvxor size x y) p))
  :hints (("Goal" :in-theory (enable fep))))

(defthm fep-of-bvcat
  (implies (and (< (expt 2 (+ highsize lowsize)) p)
                (natp highsize)
                (natp lowsize)
                (integerp p))
           (fep (acl2::bvcat highsize highval lowsize lowval)
                p))
  :hints (("Goal" :cases ((natp highsize))
           :in-theory (enable fep))))

(defthm fep-of-bitxor
  (implies (<= 2 p)
           (fep (acl2::bitxor x y) p))
  :hints (("Goal" :in-theory (enable fep))))

(defthmd bvnot-becomes-add-of-neg
  (implies (and (< (expt 2 n) p)
                (posp n)
                (posp p))
           (equal (acl2::bvnot n x)
                  (add (+ -1 (expt 2 n))
                       (neg (acl2::bvchop n x)
                            p)
                       p)))
  :hints (("Goal" :in-theory (enable acl2::bvnot lognot
                                     acl2::bvchop-of-sum-cases neg add
                                     acl2::mod-sum-cases))))

(defthm add-of-bvnot-becomes-add-of-neg
  (implies (and (integerp y)
                (integerp x)
                (posp n)
                (posp p))
           (equal (add x (acl2::bvnot n y) p)
                  (add (+ -1 (expt 2 n)) (add x (neg (acl2::bvchop n y) p) p) p)))
  :hints (("Goal" :in-theory (enable acl2::bvnot lognot acl2::bvchop-of-sum-cases neg add))))

(defthm add-of-bvnot-becomes-add-of-neg-arg2
  (implies (and (integerp y)
                (integerp x)
                (posp n)
                (posp p))
           (equal (add (acl2::bvnot n y) x
                       p)
                  (add (+ -1 (expt 2 n))
                       (add (neg (acl2::bvchop n y)
                                 p)
                            x
                            p)
                       p)))
  :hints (("Goal" :in-theory (enable acl2::bvnot lognot acl2::bvchop-of-sum-cases neg add))))

(defthm unsigned-byte-p-of-add
  (implies (and (unsigned-byte-p (+ -1 n) x)
                (unsigned-byte-p (+ -1 n) y)
                (posp p)
                (posp n)
                (< (expt 2 n) p) ; tighten?
                )
           (unsigned-byte-p n (add x y p)))
  :hints (("Goal" :in-theory (enable add))))
