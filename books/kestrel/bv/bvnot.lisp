; Logical negation of a bit-vector
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "getbit")
(include-book "lognot")
(include-book "unsigned-byte-p")
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/arithmetic-light/minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt2" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))

;; ;move and rename
;; (defthm +-cancel-helper
;;   (equal (equal x (+ y x))
;;          (and (acl2-numberp x)
;;               (equal (fix y) 0))))

(defund bvnot (size x)
  (declare (type integer x)
           (type (integer 0 *) size))
  (bvchop size (lognot x)))

(in-theory (disable lognot))

(defthm unsigned-byte-p-of-bvnot
  (implies (<= size size2)
           (equal (unsigned-byte-p size2 (bvnot size val))
                  (natp size2)))
  :hints (("Goal" :in-theory (enable bvnot))))

(defthm bvnot-when-size-is-not-positive
  (implies (<= size 0)
           (equal (bvnot size x)
                  0))
  :hints (("Goal" :in-theory (enable bvnot))))

;drop?
(defthm bvnot-when-not-natp-size
  (implies (not (natp size))
           (equal (bvnot size x)
                  0))
  :hints (("Goal" :in-theory (e/d (bvnot) nil))))

(defthm bvnot-when-size-is-not-integerp
  (implies (not (integerp size))
           (equal (bvnot size x)
                  0))
  :hints (("Goal" :in-theory (enable bvnot))))

(defthm getbit-0-of-bvnot
  (implies (posp size)
           (equal (getbit 0 (bvnot size x))
                  (bvnot 1 x)))
  :hints (("Goal" :in-theory (enable bvnot))))


(defthm bvchop-of-bvnot-same
  (equal (bvchop size (bvnot size val))
         (bvnot size val)))

(defthm bvnot-of-bvchop
  (implies (and (<= size size2)
                (integerp size2))
           (equal (bvnot size (bvchop size2 x))
                  (bvnot size x)))
  :hints (("Goal"
           :cases ((acl2-numberp x))
           :in-theory (enable bvnot lognot bvchop-when-i-is-not-an-integer))))

(defthm bvnot-of-bvchop-same
  (equal (bvnot size (bvchop size x))
         (bvnot size x))
  :hints (("Goal"
           :cases ((acl2-numberp x))
           :in-theory (enable bvnot lognot bvchop-when-i-is-not-an-integer))))

(defthm bvchop-lognot-bvchop
  (equal (bvchop n (lognot (bvchop n x)))
         (bvchop n (lognot x)))
  :hints (("Goal" :in-theory (e/d (lognot)
                                  (bvchop-1-becomes-getbit)))))

(defthm bvnot-of-bvnot
  (equal (bvnot size (bvnot size x))
         (bvchop size x))
  :hints (("Goal" :in-theory (enable bvnot))))

(defthm bvchop-lognot-bvchop-1
  (equal (bvchop 1 (lognot (bvchop 1 x)))
         (bvchop 1 (lognot x)))
  :hints (("Goal" :in-theory (e/d (lognot) (bvchop-1-becomes-getbit
                                            bvchop-chop-leading-constant)))))

(defthm logtail-of-lognot
  (equal (logtail n (lognot x))
         (lognot (logtail n x)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (logtail lognot floor-of-sum equal-of-0-and-mod)
                           (;mod-cancel
                            floor-minus-arg1-hack)))))

(defthmd lognot-of-logtail
  (equal (lognot (logtail n x))
         (logtail n (lognot x)))
  :hints (("Goal" :by logtail-of-lognot)))

(theory-invariant (incompatible (:rewrite lognot-of-logtail) (:rewrite logtail-of-lognot)))

(defthm getbit-of-bvnot
  (implies (and (< n m)
                (natp n)
                (natp m)
                ;(integerp x)
                )
           (equal (getbit n (bvnot m x))
                  (bvnot 1 (getbit n x))))
  :hints (("Goal"
           :use (:instance BVCHOP-LOGNOT-BVCHOP-1 (X (LOGTAIL N X)))
           :in-theory (e/d (bvnot getbit slice)
                           (BVCHOP-LOGNOT-BVCHOP-1
                            BVCHOP-LOGNOT-BVCHOP
                            slice-becomes-getbit ;LOGTAIL-BVCHOP
                            bvchop-1-becomes-getbit BVCHOP-OF-LOGTAIL-BECOMES-SLICE)))))

;rename and gen
(defthm getbit-1-of-bvnot-1
  (equal (getbit 1 (bvnot 1 x))
         0)
  :hints (("Goal" :in-theory (enable bvnot))))
