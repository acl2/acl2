; Mixed bit-vector theorems
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "bvchop")
(include-book "slice")
(include-book "getbit")
(include-book "bvplus")
;(include-book "bvminus")
(include-book "bvmult")
(include-book "bitxor")
;(include-book "bvcat")
;(include-book "bvuminus")
(include-book "unsigned-byte-p")
(include-book "bitand")
(local (include-book "kestrel/arithmetic-light/expt2" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))

;; TODO: eventually split up this book

;; A 1-bit product is just an AND.
(defthm bvmult-1-becomes-bitand
  (equal (bvmult 1 x y)
         (bitand x y))
  :hints (("Goal"
           :cases ((and (equal 1 (getbit 0 x)) (equal 1 (getbit 0 y)))
                   (and (not (equal 1 (getbit 0 x))) (equal 1 (getbit 0 y)))
                   (and (equal 1 (getbit 0 x)) (not (equal 1 (getbit 0 y)))))
           :use ((:instance bvmult-of-bvchop-arg2 (size 1))
                 (:instance bvmult-of-bvchop-arg2 (size 1) (x y) (y 1))
                 (:instance bvmult-of-bvchop-arg2 (size 1) (x y) (y 0)))
           :in-theory (e/d (bitand bvand ;bvmult
                                   getbit-when-val-is-not-an-integer)
                           (bvmult-of-bvchop-arg2)))))

;; A 1-bit sum is just an XOR.
(defthm bvplus-1-becomes-bitxor
  (equal (bvplus 1 x y)
         (bitxor x y))
  :hints (("Goal"
           :cases ((and (equal 1 (getbit 0 x)) (equal 1 (getbit 0 y)))
                   (and (not (equal 1 (getbit 0 x))) (equal 1 (getbit 0 y)))
                   (and (equal 1 (getbit 0 x)) (not (equal 1 (getbit 0 y)))))
           :use ((:instance bvplus-of-bvchop-arg2 (size 1))
                 (:instance bvplus-of-bvchop-arg2 (size 1) (x y) (y 1))
                 (:instance bvplus-of-bvchop-arg2 (size 1) (x y) (y 0)))
           :in-theory (e/d (bitand  getbit-when-val-is-not-an-integer)
                           (bvplus-of-bvchop-arg2)))))
