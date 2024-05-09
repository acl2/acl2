; Validation proofs for SHA-3 spec
;
; Copyright (C) 2019-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "SHA3")

(include-book "sha-3")
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/arithmetic-light/minus" :dir :system))
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/lists-light/firstn" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
(local (include-book "kestrel/bv/unsigned-byte-p" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod2" :dir :system))
(local (include-book "kestrel/arithmetic-light/ceiling" :dir :system))

;;
;; Correctness of string to state-array conversion
;;

(defthm nth-plane-of-map-bit-string-to-plane
  (implies (and (posp w)
                (all-bit-stringp bit-lists)
                (true-listp bit-lists)
                (items-have-len (* 5 w) bit-lists)
                (natp n)
                (force (< n (len bit-lists))))
           (equal (nth-plane n (map-bit-string-to-plane bit-lists w) w)
                  (bit-string-to-plane (nth n bit-lists) w)))
  :hints (("Goal" :in-theory (enable NTH-PLANE nth))))

(local
 (defthmd helper
   (implies (and (<= X 4)
                 (natp x)
                 (posp w))
            (<= (* w x) (* 4 w)))
   :rule-classes :linear))

(defthm bits-to-state-array-correct
  (implies (and (posp w)
                (bit-stringp s)
                (equal (len s) (* 25 w))
                (natp x)
                (< x 5)
                (natp y)
                (< y 5)
                (natp z)
                (< z w)
                )
           (equal (a x y z (bits-to-state-array s w) w)
                  (nth (+ (* w (+ (* 5 y) x)) z)
                       s)))
  :otf-flg t
  :hints (("Goal"
           :in-theory (enable bits-to-state-array
                              BIT-STRING-TO-PLANE NTH-LANE helper a
                              nth-bit ;todo
                              ))))

;;;
;;; Correctness of theta
;;;

(defun lane-n-induct (z x a w n)
  (declare (xargs :measure (nfix (+ 1 (- w z)))))
  (if (or (not (mbt (natp z)))
          (not (mbt (natp w)))
          (<= w z))
      (list z x a w n)
    (lane-n-induct (+ 1 z) x a w (+ -1 n))))

(defthm nth-bit-of-theta-c-lane
  (implies (and (natp n)
                (< n (- w z))
                (w-valp w)
                (natp z)
                (natp x)
                (< x 5))
           (equal (nth-bit n (theta-c-lane z x a w) w)
                  (let ((z (+ n z)))
                    (bitxor (a x 0 z a w)
                            (bitxor (a x 1 z a w)
                                    (bitxor (a x 2 z a w)
                                            (bitxor (a x 3 z a w)
                                                    (a x 4 z a w))))))))
  :hints (("Goal" :induct (lane-n-induct z x a w n)
           :in-theory (enable theta-c-lane nth-bit))))

(defun lanes-n-induct (x a w n)
  (declare (xargs :measure (nfix (+ 1 (- 5 x)))))
  (if (or (not (mbt (natp x)))
          (<= 5 x))
      (list x a w n)
    (lanes-n-induct (+ 1 x) a w (+ -1 n))))

(defthm nth-lane-of-theta-c-lanes
  (implies (and (natp n)
                (< n (- 5 x))
                (w-valp w)
                (state-arrayp a w)
                (natp n)
;               (< x 5)
                (natp x))
           (equal (nth-lane n (theta-c-lanes x a w) w)
                  (theta-c-lane 0 (+ x n) a w)))
  :hints (("Goal" :induct (lanes-n-induct x a w n)
           :in-theory (enable NTH-LANE theta-c-lanes))))

;; C[x,z] = ... (Algorithm 1, Step 1)
(defthm theta-c-correct
  (implies (and (w-valp w)
                (state-arrayp a w)
                (< x 5)
                (natp x)
                (natp z)
                (< z w))
           (equal (nth-bit z (nth-lane x (theta-c a w) w) w)
                  (bitxor (a x 0 z a w)
                          (bitxor (a x 1 z a w)
                                  (bitxor (a x 2 z a w)
                                          (bitxor (a x 3 z a w)
                                                  (a x 4 z a w))))))))

(defthm nth-bit-of-theta-d-lane
  (implies (and (natp n)
                (< n (- w z))
                (w-valp w)
                (natp z)
                (natp x)
                (< x 5))
           (equal (nth-bit n (theta-d-lane z x c w) w)
                  (let ((z (+ n z)))
                    (bitxor (nth-bit z               (nth-lane (mod (- x 1) 5) c w) w)
                            (nth-bit (mod (- z 1) w) (nth-lane (mod (+ x 1) 5) c w) w)))))
  :hints (("Goal" :induct (lane-n-induct z x a w n)
           :in-theory (enable theta-d-lane nth-bit))))

(defun lanes-d-induct (x w n)
  (declare (xargs :measure (nfix (+ 1 (- 5 x)))))
  (if (or (not (mbt (natp x)))
          (<= 5 x))
      (list x w n)
    (lanes-d-induct (+ 1 x) w (+ -1 n))))

(defthm nth-lane-of-theta-d-lanes
  (implies (and (natp n)
                (< n (- 5 x))
                (w-valp w)
                (state-arrayp a w)
                (natp n)
;               (< x 5)
                (natp x))
           (equal (nth-lane n (theta-d-lanes x c w) w)
                  (theta-d-lane 0 (+ x n) c w)))
  :hints (("Goal" :induct (lanes-d-induct x w n)
           :in-theory (enable NTH-LANE theta-d-lanes))))

(defthm nth-lane-of-theta-d
  (implies (and (natp n)
                (< n 5)
                (w-valp w)
                (state-arrayp a w)
                (natp n))
           (equal (nth-lane n (theta-d c w) w)
                  (theta-d-lane 0 n c w)))
  :hints (("Goal" :in-theory (enable theta-d))))

;; D[x,z] = ... (Algorithm 1, Step 2)
(defthm theta-d-correct
  (implies (and (w-valp w)
                (state-arrayp a w)
                (planep c w)
                (natp x)
                (< x 5)
                (natp z)
                (< z w))
           (equal (nth-bit z (nth-lane x (theta-d c w) w) w)
                  (bitxor (nth-bit z               (nth-lane (mod (- x 1) 5) c w) w)
                          (nth-bit (mod (- z 1) w) (nth-lane (mod (+ x 1) 5) c w) w)))))

(defthm nth-lane-of-theta-lanes
  (implies (and (natp n)
                (< n (- 5 x))
                (w-valp w)
                (state-arrayp a w)
                (natp n)
                (natp x))
           (equal (nth-lane n (theta-lanes x y a d w) w)
                  (theta-lane 0 (+ x n) y a d w)))
  :hints (("Goal" :induct (lanes-n-induct x a w n)
           :in-theory (enable NTH-LANE theta-lanes))))

(defthm nth-bit-of-theta-lane
  (implies (and (natp n)
                (< n (- w z))
                (w-valp w)
                (natp z)
                (natp x)
                (< x 5))
           (equal (nth-bit n (theta-lane z x y a d w) w)
                  (let ((z (+ n z)))
                    (bitxor (a x y z a w)
                            (nth-bit z (nth-lane x d w) w)))))
  :hints (("Goal" :induct (lane-n-induct z x a w n)
           :in-theory (enable theta-lane nth-bit))))

(defthm nth-plane-of-theta-planes
  (implies (and (natp n)
                (< n (- 5 y))
                (w-valp w)
                (state-arrayp a w)
                (natp n)
;               (< x 5)
                (natp y))
           (equal (nth-plane n (theta-planes y a d w) w)
                  (theta-lanes 0 (+ y n) a d w)))
  :hints (("Goal" :induct (planes-n-induct y a w n)
           :in-theory (enable NTH-pLANE theta-planes))))

;; A'[x,y,z] = A[x,y,z] xor D[x,z] (Algorithm 1, Step 3)
(defthm theta-correct
  (implies (and (state-arrayp a w)
                (w-valp w)
                (natp x)
                (< x 5)
                (natp y)
                (< y 5)
                (natp z)
                (< z w))
           (equal (a x y z (theta a w) w)
                  (bitxor (a x y z a w)
                          (nth-bit z (nth-lane x (theta-d (theta-c a w) w) w) w))))
  :hints (("Goal" :in-theory (enable a ;theta-d
                                     ;;NTH-PLANE NTH-LANE NTH-bit
                                     theta
                                     ))))

;;;
;;; Correctness of rho
;;;

;; todo: check rho using the table of offsets


;;;
;;; Correctness of pi
;;;

(defthm nth-lane-of-pi-lanes
  (implies (and (natp n)
                (< n (- 5 x))
                (w-valp w)
                (state-arrayp a w)
                (natp n)
                (natp x))
           (equal (nth-lane n (pi-lanes x y a w) w)
                  (get-lane (mod (+ x n (* 3 y)) 5) (+ x n) a w)))
  :hints (("Goal" :induct (lanes-n-induct x a w n)
           :in-theory (enable NTH-LANE pi-lanes))))

(defthm nth-plane-of-pi-planes
  (implies (and (natp n)
                (< n (- 5 y))
                (w-valp w)
                (state-arrayp a w)
                (natp n)
                (natp y))
           (equal (nth-plane n (pi-planes y a w) w)
                  (pi-lanes 0 (+ y n) a w)))
  :hints (("Goal" :induct (planes-n-induct y a w n)
           :in-theory (enable NTH-pLANE pi-planes))))

;; Prove that pi is as described in Sec 3.2.3.
(defthm pi-correct
  (implies (and (state-arrayp a w)
                (w-valp w)
                (natp x)
                (< x 5)
                (natp y)
                (< y 5)
                (natp z)
                (< z w))
           (equal (a x y z (pi-fn a w) w)
                  (a (mod (+ x (* 3 y)) 5) x z a w)))
  :hints (("Goal" :in-theory (enable a ;theta-d
                                     ;;NTH-PLANE NTH-LANE NTH-bit
                                     pi-fn))))

;;;
;;; Correctness of chi
;;;

(defthm getbit-of-0-and-*-becomes-bitand
  (implies (and (integerp x)
                (integerp y)
                )
           (equal (acl2::getbit 0 (* x y))
                  (bitand x y)))
  :hints (("Goal" :cases ((equal 0 (mod x 2)))
           :in-theory (e/d (acl2::getbit acl2::bvchop acl2::slice bitand acl2::bvand)
                           (acl2::bvchop-1-becomes-getbit
                            acl2::slice-becomes-getbit
                            acl2::slice-becomes-bvchop
                            acl2::bvchop-of-logtail-becomes-slice)))))

(defthm <-of-if-arg1
  (equal (< (if test a b) c)
         (if test (< a c) (< b c))))

(defthm nth-bit-of-chi-lane
  (implies (and (natp n)
                (< n (- w z))
                (w-valp w)
                (natp z)
                (natp x)
                (natp y)
                (< y 5)
                (state-arrayp a w))
           (equal (nth-bit n (chi-lane z x y a w) w)
                  (let ((z (+ n z)))
                    (bitxor (a x y z a w)
                            (* (bitxor (a (mod (+ x 1) 5) y z a w)
                                       1)
                               (a (mod (+ x 2) 5) y z a w))))))
  :hints (("Goal" :induct (lane-n-induct z x a w n)
           :in-theory (enable chi-lane nth-bit))))

(defthm nth-lane-of-chi-lanes
  (implies (and (natp n)
                (< n (- 5 x))
                (w-valp w)
                (state-arrayp a w)
                (natp n)
                (natp x))
           (equal (nth-lane n (chi-lanes x y a w) w)
                  (chi-lane 0 (+ x n) y a w)))
  :hints (("Goal" :induct (lanes-n-induct x a w n)
           :in-theory (enable NTH-LANE chi-lanes))))

(defthm nth-plane-of-chi-planes
  (implies (and (natp n)
                (< n (- 5 y))
                (w-valp w)
                (state-arrayp a w)
                (natp n)
                (natp y))
           (equal (nth-plane n (chi-planes y a w) w)
                  (chi-lanes 0 (+ y n) a w)))
  :hints (("Goal" :induct (planes-n-induct y a w n)
           :in-theory (enable NTH-pLANE chi-planes))))

;; Prove that chi is as described in Sec 3.2.4.
(defthm chi-correct
  (implies (and (state-arrayp a w)
                (w-valp w)
                (natp x)
                (< x 5)
                (natp y)
                (< y 5)
                (natp z)
                (< z w))
           (equal (a x y z (chi a w) w)
                  (bitxor (a x y z a w)
                          (* (bitxor (a (mod (+ x 1) 5) y z a w)
                                     1)
                             (a (mod (+ x 2) 5) y z a w)))))
  :hints (("Goal" :in-theory (enable a ;theta-d
                                     ;;NTH-PLANE NTH-LANE NTH-bit
                                     chi))))


;;;
;;; Validation of keccak-sponge
;;;

(defthm len-of-keccak-sponge-aux2
  (implies (and (natp d)
                (posp r))
           (equal (len (keccak-sponge-aux2 b n_r r z s d))
                  d)))

;; Check that the length of the output is in fact d.
(defthm len-of-keccak-sponge
  (implies (and (natp d)
                (posp r))
           (equal (len (keccak-sponge b n_r r n d))
                  d)))
