; A book about discarding irrelevant array values
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "bv-array-read")
(include-book "kestrel/bv/bvmult" :dir :system)
(include-book "kestrel/bv/bvplus" :dir :system)

(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod2" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
;(local (include-book "kestrel/arithmetic-light/floor-and-mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus-and-minus" :dir :system))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/revappend" :dir :system))

;; (defun keep-vals-with-congruent-indices (index vals residue modulus)
;;   (declare (xargs :measure (len vals)))
;;   (if (endp vals)
;;       nil
;;     (if (equal residue (mod index modulus))
;;         (cons (first vals)
;;               (keep-vals-with-congruent-indices (+ 1 index) (rest vals) residue modulus))
;;       (keep-vals-with-congruent-indices (+ 1 index) (rest vals) residue modulus))))

;; ;; (keep-vals-with-congruent-indices 0 '(0 1 2 3 4 5 6 7 8) 2 3)

;; (local
;;  (defun ind (index vals n)
;;    (if (endp vals)
;;        (list index vals n)
;;      (ind (+ 1 index) (rest vals) (+ -1 n)))))

;; (defthmd nth-of-*-helper
;;   (implies (and (natp k)
;;                 (natp n)
;;                 (natp index)
;;                 (equal (mod index k) 0))
;;            (equal (nth (* k n) vals)
;;                   (nth n (keep-vals-with-congruent-indices index vals 0 k))))
;;   :hints (("Goal" :induct (ind index vals n))))

(defund every-nth-exec-aux (n vals acc)
  (declare (xargs :guard (and (posp n)
                              (true-listp vals)
                              (true-listp acc))
                  :measure (len vals)
                  ))
  (if (not (mbt (posp n))) ; for termination
      nil
    (if (endp vals)
        (reverse acc)
      (every-nth-exec-aux n (nthcdr n vals) (cons (first vals) acc)))))

(defund every-nth-exec (n vals)
  (declare (xargs :guard (and (posp n)
                              (true-listp vals))))
  (every-nth-exec-aux n vals nil))

(defund every-nth (n vals)
  (declare (xargs :guard (and (posp n)
                              (true-listp vals))
                  :verify-guards nil ; done below
                  :measure (len vals)
                  ))
  (mbe :logic
       (if (not (mbt (posp n))) ; for termination
           nil
         (if (endp vals)
             nil
           (cons (first vals)
                 (every-nth n (nthcdr n vals)))))
       :exec (every-nth-exec n vals)))

(defthm every-nth-exec-aux-helper
  (implies (and (true-listp acc)
                (posp n))
           (equal (every-nth-exec-aux n vals acc)
                  (append (reverse acc)
                          (every-nth n vals))))
  :hints (("Goal" :in-theory (enable every-nth every-nth-exec-aux))))

(verify-guards every-nth :hints (("Goal" :in-theory (enable every-nth-exec every-nth))))

; (equal (every-nth 3 '(0 1 2 3 4 5 6 7 8 9 10)) '(0 3 6 9))

(defthm consp-of-every-nth
  (implies (posp n)
           (equal (consp (every-nth n vals))
                  (consp vals)))
  :hints (("Goal" :in-theory (enable every-nth))))

(local
 (defun ind (n vals n2)
   (declare (xargs :measure (len vals)))
   (if (not (posp n2))
       nil
     (if (endp vals)
         (list n vals n2)
       (ind (- n 1) (nthcdr n2 vals) n2)))))

(defthm nth-of-every-nth
  (implies (and (posp n2)
                (natp n))
           (equal (nth n (every-nth n2 vals))
                  (nth (* n n2) vals)))
  :hints (("Goal" :in-theory (enable every-nth)
           :induct (ind n vals n2))))

(defthmd nth-when-remainder-known
  (implies (and (equal remainder (mod index modulus))
                (natp index)
                (posp modulus))
           (equal (nth index vals)
                  (nth (floor index modulus) (every-nth modulus (nthcdr remainder vals))))))

(defthm bv-array-read-of-bvmult-discard-vals
  (implies (and (syntaxp (and (quotep data)
                              (quotep k)
                              (quotep index-width)
                              (quotep len)))
                (equal len (expt 2 index-width)) ; gen? or other rules might help establish this
                (< (* k index) len) ; gen? the bvmult doesn't do any real chopping
                (integerp (/ len k)) ; gen? requires k to be a power of 2
                (< 1 k)
                (natp index)
                (natp index-width)
                (integerp k))
           (equal (bv-array-read element-size len (bvmult index-width k index) data)
                  ;; The call to every-nth gets evaluated:
                  (bv-array-read element-size (/ len k) index (every-nth k data))))
  :hints (("Goal" :in-theory (enable bv-array-read bvmult unsigned-byte-p))))

;; a variant for index n*k+i where i<k
(defthm bv-array-read-of-bvplus-of-bvmult-discard-vals
  (implies (and (syntaxp (and (quotep data)
                              (quotep k)
                              (quotep i)
                              (quotep index-width)
                              (quotep len)))
                (equal len (expt 2 index-width)) ; gen? or other rules might help establish this
                (< i k)
                (< (+ i (* k index)) len) ; gen? the bvmult doesn't do any real chopping
                (integerp (/ len k)) ; gen? requires k to be a power of 2
                (< 1 k)
                (natp index)
                (natp i)
                (natp index-width)
                (integerp k))
           (equal (bv-array-read element-size len (bvplus index-width i (bvmult index-width k index)) data)
                  ;; The call to every-nth gets evaluated:
                  (bv-array-read element-size (/ len k) index (every-nth k (nthcdr i data)))))
  :hints (("Goal" :in-theory (enable bv-array-read bvmult bvplus unsigned-byte-p))))
