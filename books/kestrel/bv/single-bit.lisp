; Rules about single-bit operations
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2016-2020 Kestrel Technology, LLC
; Copyright (C) 2013-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "bitnot")
(include-book "bitand")
(include-book "bitxor")
(include-book "bitor")

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
         (bitnot x)))

(defthmd bitnot-becomes-bitxor-with-1
  (equal (bitnot x)
         (bitxor 1 x))
  :hints (("Goal" :cases ((equal 0 x)
                          (equal 1 x))
           :in-theory (enable bvnot bitnot))))

;(in-theory (disable bitxor-of-1-becomes-bitnot-arg1)) ;which way should we go on this?
(theory-invariant (incompatible (:rewrite bitnot-becomes-bitxor-with-1) (:rewrite bitxor-of-1-becomes-bitnot-arg1)))

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
         (getbit 0 x)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm bitor-x-bitxor-1-x
  (implies (unsigned-byte-p 1 x)
           (equal (bitor x (bitxor 1 x))
                  1))
  :hints (("Goal" :cases ((equal 0 x))
           :in-theory (enable bitnot))))

(defthm bitor-x-bitxor-1-x-alt
  (implies (unsigned-byte-p 1 x)
           (equal (bitor (bitxor 1 x) x)
                  1))
  :hints (("Goal" :cases ((equal 0 x))
           :in-theory (enable bitnot))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;make a bvxor version
;subsumes the versions for 0 and 1
;the remaining 1 here isn't too bad, since 0 will be dropped and anything else will be trimmed
(defthm equal-of-constant-and-bitxor-1
  (implies (syntaxp (quotep k))
           (equal (equal k (bitxor 1 x))
                  (and (unsigned-byte-p 1 k)
                       (equal (getbit 0 x) (bitnot k)))))
  :hints (("Goal" :cases ((equal 0 (getbit 0 x)))
           :in-theory (e/d (bitnot-becomes-bitxor-with-1)
                           (bitxor-of-1-becomes-bitnot-arg1 bvxor-1-becomes-bitxor)))))

(defthm equal-of-bitxor-and-bitor
  (equal (equal (bitxor x y) (bitor x y))
         (equal 0 (bitand x y)))
  :hints (("Goal" :cases ((equal 1 (getbit 0 x))))))
