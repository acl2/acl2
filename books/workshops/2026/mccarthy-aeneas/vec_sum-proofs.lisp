; The extracted Vec sum loop equals a recursive fold spec, for all inputs.
; Exercises Vec + an indexed loop + verification together.
(in-package "ACL2")
(include-book "vec_sum")
(include-book "tea-bridges")            ; u32-wrapping-add = bvplus bridge
(local (include-book "kestrel/bv/rules" :dir :system))

;; Spec: wrapping sum of v[i], v[i+1], ..., accumulated into s.
(defun vsum-spec (v s i)
  (declare (xargs :measure (nfix (- (len v) (nfix i)))))
  (if (and (natp i) (< i (len v)))
      (vsum-spec v (bvplus 32 s (nth i v)) (+ i 1))
    s))

(defun all-u32p (v) (if (endp v) t (and (u32p (car v)) (all-u32p (cdr v)))))

(defthm integerp-when-u32p
  (implies (u32p x) (integerp x))
  :rule-classes (:forward-chaining :rewrite))

(defthm u32p-of-nth-when-all-u32p
  (implies (and (all-u32p v) (natp i) (< i (len v))) (u32p (nth i v))))

;; Type facts that keep the loop invariant closed under a round.
(defthm u32p-of-bvplus-32
  (u32p (bvplus 32 x y))
  :hints (("Goal" :in-theory (enable u32p))))

;; usize add of an in-range index succeeds (a Vec's length fits usize).
(defthm usize-add-1-when-small
  (implies (and (natp i) (unsigned-byte-p 64 (+ i 1)))
           (equal (usize-add i 1) (ok (+ i 1))))
  :hints (("Goal" :in-theory (enable usize-add usizep unsigned-byte-p))))

(local (in-theory (enable u32-wrapping-add-is-bvplus)))
(local (in-theory (disable u32-wrapping-add)))  ; force the bridge, not the mod def

;; The extracted loop computes the spec fold (given fuel, u32 elements, and a
;; length that fits usize -- which every real Vec satisfies).
(defthm vec-sum-loop0-is-spec
  (implies (and (all-u32p v) (u32p s) (natp i) (<= i (len v))
                (unsigned-byte-p 64 (len v))
                (natp fuel) (< (- (len v) i) fuel))
           (equal (vec-sum-sum-loop0 fuel v s i)
                  (ok (vsum-spec v s i))))
  :hints (("Goal" :induct (vec-sum-sum-loop0 fuel v s i)
                  :in-theory (enable vec-sum-sum-loop0 vec-len array-index))))

(defthm vec-sum-is-spec
  (implies (and (all-u32p v) (unsigned-byte-p 64 (len v))
                (natp fuel) (< (len v) fuel))
           (equal (vec-sum-sum fuel v) (ok (vsum-spec v 0 0)))))
