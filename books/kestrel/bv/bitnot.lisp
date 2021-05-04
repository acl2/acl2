; Logical negation of a bit
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "bvnot")

(defund bitnot (x)
  (declare (type integer x))
  (if (= (bvchop 1 x) 0)
      1
    0))

(defthm bitnot-type
  (or (equal 0 (bitnot x))
      (equal 1 (bitnot x)))
  :rule-classes :type-prescription)

(in-theory (disable (:type-prescription bitnot))) ;our rule is better

(defthm integerp-of-bitnot
  (integerp (bitnot x)))

(defthm natp-of-bitnot
  (natp (bitnot x)))

(defthm bitnot-of-bitnot
  (equal (bitnot (bitnot x))
         (bvchop 1 x))
  :hints (("Goal" :in-theory (enable bitnot))))

(defthm bitnot-of-getbit-0
  (equal (bitnot (getbit 0 x))
         (bitnot x))
  :hints (("Goal" :in-theory (enable bitnot))))

(defthm getbit-0-of-bitnot
  (equal (getbit 0 (bitnot x))
         (bitnot x))
  :hints (("Goal" :in-theory (enable bitnot))))

(defthm unsigned-byte-p-of-bitnot
  (implies (posp size)
           (unsigned-byte-p size (bitnot x)))
  :hints (("Goal" :in-theory (enable bitnot))))

(defthm bitnot-equal-0-rewrite
  (equal (equal (bitnot x) 0)
         (equal 1 (getbit 0 x)))
  :hints (("Goal" :in-theory (enable bitnot))))

;gen
(defthm equal-of-1-and-bitnot
  (equal (equal 1 (bitnot x))
         (equal 0 (getbit 0 x)))
  :hints (("Goal" :in-theory (enable bitnot))))

;justifies the correctness of some operations performed by Axe
(defthmd unsigned-byte-p-1-of-bitnot
  (unsigned-byte-p 1 (bitnot x)))

(defthm bitp-of-bitnot
  (bitp (bitnot x)))

(defthm equal-of-bitnot-and-bitnot
  (equal (equal (bitnot x) (bitnot y))
         (equal (getbit 0 x) (getbit 0 y)))
  :hints (("Goal" :in-theory (enable bitnot))))

(defthmd bitnot-becomes-subtract
  (implies (bitp x)
           (equal (bitnot x)
                  (- 1 x)))
  :hints (("Goal" :cases ((equal 0 x)))))

(defthm getbit-of-1-and-+-of-2
  (implies (integerp x)
           (equal (getbit 1 (+ 2 x))
                  (bitnot (getbit 1 x))))
  :hints (("Goal" :in-theory (e/d (getbit slice bitnot)
                                  (slice-becomes-getbit
                                   bvchop-1-becomes-getbit
                                   bvchop-of-logtail-becomes-slice)))))

(local
 (defthmd bvnot-1-becomes-bitnot
   (implies (unsigned-byte-p 1 x)
            (equal (bvnot 1 x)
                   (bitnot x)))
   :hints (("Goal" :cases ((equal 0 x)
                           (equal 1 x))
            :in-theory (enable bvnot bitnot)))))

(defthm bvnot-1-of-getbit-0
   (equal (bvnot 1 (getbit 0 x))
          (bvnot 1 x))
   :hints (("Goal" :use ((:instance usb1-cases (x (getbit 0 x)))
                         (:instance bvchop-lognot-bvchop-1))
;            :expand ((BVCHOP 1 X))
            :in-theory (e/d (getbit
                             bvnot ;bozo
                             ) (getbit-when-equal-of-constant-and-bvchop-constant-version
                                bvchop-lognot-bvchop-1
                                bvchop-lognot-bvchop
                                bvchop-1-becomes-getbit
                                slice-becomes-getbit
                                GETBIT-TYPE
                                UNSIGNED-BYTE-P-OF-GETBIT)))))

;fixme redo things to go to bitnot and bitxor and redo rules to trigger on those?
(defthm bvnot-1-becomes-bitnot-better
  (equal (bvnot 1 x)
         (bitnot x))
  :hints (("Goal" :use (:instance bvnot-1-becomes-bitnot (x (getbit 0 x)))
           :in-theory (disable bvnot-1-becomes-bitnot
                               BITNOT-OF-GETBIT-0))))

(defthmd bitnot-becomes-bvnot
  (equal (bitnot x)
         (bvnot 1 x))
  :hints (("Goal" :use (:instance bvnot-1-becomes-bitnot-better))))

(theory-invariant (incompatible (:rewrite bitnot-becomes-bvnot) (:rewrite bvnot-1-becomes-bitnot-better)))

(defthm bitnot-not-equal-constant
  (implies (and (syntaxp (quotep k))
                (not (unsigned-byte-p 1 k)))
           (not (equal (bitnot x) k))))
