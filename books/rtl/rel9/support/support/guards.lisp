; RTL - A Formal Theory of Register-Transfer Logic and Computer Arithmetic
; Copyright (C) 1995-2013 Advanced Mirco Devices, Inc.
;
; Contact:
;   David Russinoff
;   1106 W 9th St., Austin, TX 78703
;   http://www.russsinoff.com/
;
; See license file books/rtl/rel9/license.txt.
;
; Author: David M. Russinoff (david@russinoff.com)

(in-package "ACL2")

; Proof of bits-guard:

; (logand (ash x (- j)) (1- (ash 1 (1+ (- i j)))))
; =
; (logand (fl (/ x (expt 2 j))) (1- (expt 2 (1+ (- i j)))))
; = {logand-slice}
; (bits (fl (/ x (expt 2 j))) (- i j) 0)
; = {bits-shift-down-1}
; (bits x i j)

(include-book "rtl")
(local (include-book "top1"))
(local (in-theory (theory 'lib-top1)))

(local-defthmd bits-guard
  (implies (and (natp x)
                (natp i)
                (natp j)
                (<= j i))
           (equal (bits x i j)
                  (logand (ash x (- j)) (1- (ash 1 (1+ (- i j)))))))
  :hints (("Goal" :in-theory (enable bits-shift-down-1 floor-fl expt-minus)
           :use ((:instance logand-slice
                            (x (ash x (- j)))
                            (n (1+ (- i j)))
                            (k 0))))))

(verify-guards bits
               :hints (("Goal" :use bits-guard
                        :in-theory (enable bits fl-mod-zero))))

; Proof of bitn-guard:

; (bitn x i)
; = {def. of bitn}
; (bits x i i)
; = {previous thm.}
; (logand (ash x (- i)) (1- (ash 1 (1+ (- i i)))))
; =
; (logand (ash x (- i)) 1)
; = {logand-with-1}
; (if (evenp (ash x (- i))) 0 1)

(local-defthmd bitn-guard
  (implies (and (natp x)
                (natp n))
           (equal (bitn x n)
                  (if (evenp (ash x (- n))) 0 1)))
  :hints (("Goal" :in-theory (e/d (bitn logand-with-1 logand-commutative
                                        bits-guard)
                                  (bits-n-n-rewrite)))))

(verify-guards bitn
               :hints (("Goal" :use bitn-guard
                        :in-theory (e/d (bitn) (bits-n-n-rewrite)))))

(verify-guards lnot)

(verify-guards binary-cat)

(local-defthm mulcat-guard-proof-hack
  (implies (and (< 0 l)
                (integerp l)
                (not (equal n 1)))
           (not (equal l (* l n))))
  :hints (("Goal" :use ((:instance collect-constants-with-division
                                   (x n)
                                   (c1 l)
                                   (c2 l))))))

(verify-guards mulcat)

(verify-guards setbits)

(verify-guards setbitn)

(verify-guards binary-land0)

(verify-guards binary-lior0)

(verify-guards binary-lxor0)

(include-book "land")

(verify-guards binary-land
               :hints (("Goal" :use land-is-land0
                        :in-theory (enable binary-land0)
                        :expand ((binary-land x y n)))))

(include-book "lior")

(verify-guards binary-lior
               :hints (("Goal" :use lior-is-lior0
                        :in-theory (enable binary-lior0)
                        :expand ((binary-lior x y n)))))

(include-book "lxor")

(verify-guards binary-lxor
               :hints (("Goal" :use lxor-is-lxor0
                        :in-theory (enable binary-lxor0)
                        :expand ((binary-lxor x y n)))))
