; Mixed theorems about bvminus
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "bvminus")
(include-book "getbit")
(include-book "bitnot")

(defthm bvminus-of-1-and-getbit-of-0-arg2
  (equal (bvminus 1 (getbit 0 x) y)
         (bvminus 1 x y))
  :hints (("Goal" :in-theory (e/d (getbit)
                                  (bvchop-1-becomes-getbit
                                   slice-becomes-getbit)))))

(defthm bvminus-of-1-and-getbit-of-0-arg3
  (equal (bvminus 1 x (getbit 0 y))
         (bvminus 1 x y))
  :hints (("Goal" :in-theory (e/d (getbit)
                                  (bvchop-1-becomes-getbit
                                   slice-becomes-getbit)))))

(defthm bvminus-subst-arg1-constant
  (implies (and (syntaxp (not (quotep x)))
                (equal (getbit 0 x) k)
                (syntaxp (quotep k)))
           (equal (bvminus 1 x y)
                  (bvminus 1 k y))))

(defthm bvminus-subst-arg3-constant
  (implies (and (syntaxp (not (quotep y)))
                (equal (getbit 0 y) k)
                (syntaxp (quotep k)))
           (equal (bvminus 1 x y)
                  (bvminus 1 x k))))

(defthm bvminus-of-1-and-1-becomes-bitnot
 (equal (bvminus 1 1 x)
        (bitnot x))
 :hints (("Goal" :in-theory (enable bitnot))))
