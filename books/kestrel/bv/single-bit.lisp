; Rules about single-bit operations
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2016-2020 Kestrel Technology, LLC
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "bitnot")
(include-book "bitxor")

(defthm bitxor-of-bitnot-arg1
  (equal (bitxor (bitnot x) y)
         (bitnot (bitxor x y)))
  :hints (("Goal" :in-theory (e/d (bitnot bitxor bvxor) (bvxor-1-becomes-bitxor)))))

(defthm bitxor-of-bitnot-arg2
  (equal (bitxor y (bitnot x))
         (bitnot (bitxor y x)))
  :hints (("Goal" :in-theory (e/d (bitnot bitxor bvxor) (bvxor-1-becomes-bitxor)))))

(defthm bitxor-of-1-becomes-bitnot-arg1
  (equal (bitxor 1 x)
         (bitnot x))
  :hints (("Goal" :in-theory (e/d (bitxor bitnot bvxor) (bvxor-1-becomes-bitxor)))))

;drop if we commute
(defthm bitxor-of-1-becomes-bitnot-arg2
  (equal (bitxor x 1)
         (bitnot x))
  :hints (("Goal" :in-theory (enable BITXOR-COMMUTATIVE))))

(defthmd bitnot-becomes-bitxor-with-1
  (equal (bitnot x)
         (bitxor 1 x))
  :hints (("Goal" :cases ((equal 0 x)
                          (equal 1 x))
           :in-theory (enable bvnot bitnot))))

;(in-theory (disable bitxor-of-1-becomes-bitnot-arg1)) ;which way should we go on this?
(theory-invariant (incompatible (:rewrite bitnot-becomes-bitxor-with-1) (:rewrite bitxor-of-1-becomes-bitnot-arg1)))

(defthm not-equal-of-bitnot-and-getbit-0-same
  (not (equal (bitnot x) (getbit 0 x)))
  :hints (("Goal" :in-theory (enable bitnot))))

;rename
(defthm bit-equal-bitxor-rewrite
  (equal (equal (bitnot y) (bitxor x y))
         (equal 1 (getbit 0 x)))
  :hints (("Goal"   :do-not '(preprocess)
           :in-theory (e/d (;bitxor
                            ) (bvxor-1-becomes-bitxor)))))

;fixme just choose bitnot or bitxor 1...
(defthm bitnot-of-bitxor-of-1
  (equal (bitnot (bitxor 1 x))
         (getbit 0 x))
  :hints (("Goal" :in-theory (enable))))
