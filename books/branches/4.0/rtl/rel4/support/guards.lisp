(in-package "ACL2")

; Proof of bits-guard:

; (logand (ash x (- j)) (1- (ash 1 (1+ (- i j)))))
; =
; (logand (fl (/ x (expt 2 j))) (1- (expt 2 (1+ (- i j)))))
; = {logand-slice}
; (bits (fl (/ x (expt 2 j))) (- i j) 0)
; = {bits-shift-down}
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
  :hints (("Goal" :in-theory (enable bits-shift-down floor-fl expt-minus)
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

(verify-guards binary-land)

(verify-guards binary-lior)

(verify-guards binary-lxor)
