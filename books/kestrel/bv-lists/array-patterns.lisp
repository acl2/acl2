; A book about discarding irrelevant array values
;
; Copyright (C) 2022-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; TODO: These aren't really "array patterns"

(include-book "bv-array-read")
(include-book "kestrel/bv/bvmult" :dir :system)
(include-book "kestrel/bv/bvplus" :dir :system)
(include-book "kestrel/bv/bvcat" :dir :system)
(include-book "kestrel/lists-light/every-nth" :dir :system)
(local (include-book "kestrel/bv/logapp" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod2" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
;(local (include-book "kestrel/arithmetic-light/floor-and-mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/arithmetic-light/times-and-divide" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt2" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus-and-minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/ceiling" :dir :system))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/revappend" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))

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



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Discards some (usually, most) of the elements in the array:
;; Example: If we know the index is of the form 4*i, then we can discard all array values
;; whose indices are not multiples of 4.
(defthm bv-array-read-of-bvmult-discard-vals
  (implies (and (syntaxp (and (quotep data)
                              (quotep k)
                              (quotep index-width)
                              (quotep len)))
                (<= len (expt 2 index-width)) ; gen?? or other rules might help establish this
                (integerp len)
                (< (* k index) len) ; gen? the bvmult doesn't do any real chopping
                (integerp (/ len k)) ; gen? requires k to be a power of 2
                (< 1 k)
                (natp index)
                (natp index-width)
                (integerp k))
           (equal (bv-array-read element-size len (bvmult index-width k index) data)
                  ;; The call to every-nth gets evaluated:
                  (bv-array-read element-size (/ len k)
                                 index ; consider this instead: (bvchop (- index-width (lg k)) index)
                                 (every-nth k data))))
  :hints (("Goal" :in-theory (enable bv-array-read bvmult unsigned-byte-p))))

;drop the other one?
(defthm bv-array-read-of-bvmult-discard-vals-gen
  (implies (and (syntaxp (and (quotep data)
                              (quotep k)
                              (quotep index-width)
                              (quotep len)))
                (< index (/ (expt 2 index-width) k)) ; the bvmult doesn't do any real chopping ; gen in the power-of-2 case?
                (< index (/ len k))  ; the access is in bounds
                (< 1 k)
                (equal len (len data)) ; drop? (natp len)
                (natp index)
                (natp index-width)
                (integerp k))
           (equal (bv-array-read element-size len (bvmult index-width k index) data)
                  ;; The call to every-nth gets evaluated:
                  (let ((data (every-nth k data)))
                    (bv-array-read element-size (len data) index data))))
  :hints (("Goal" :in-theory (enable bv-array-read bvmult unsigned-byte-p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm bv-array-read-of-bvcat-discard-vals
  (implies (and (syntaxp (and (quotep data)
                              (quotep lowval) ; note this
                              (quotep lowsize)
                              (quotep highsize)
                              (quotep len)))
                (equal len (expt 2 (+ lowsize highsize))) ; gen? or other rules might help establish this
                (equal len (len data))
                (natp highval)
                (natp lowval)
                (natp highsize)
                (natp lowsize))
           (equal (bv-array-read element-size len (bvcat highsize highval lowsize lowval) data)
                  ;; The calls to nthcdr and every-nth get evaluated to give a smaller array:
                  (let ((data (every-nth (expt 2 lowsize) (nthcdr (bvchop lowsize lowval) data))))
                    (bv-array-read element-size (len data) (bvchop highsize highval) data))))
  :hints (("Goal" :nonlinearp t
           :in-theory (enable bv-array-read-opener
                              bvcat
                              expt-of-+
                              logapp unsigned-byte-p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Discards array values at the front that cannot be accessed
(defthm bv-array-read-of-+-of-constant-shorten
  (implies (and (syntaxp (and (quotep k)
                              (quotep vals)))
                (< (+ k index) len) ; gen?
                (natp k)
                (natp len)
                (natp index))
           (equal (bv-array-read width len (+ k index) vals)
                  (bv-array-read width (- len k) index (nthcdr k vals))))
  :hints (("Goal" :in-theory (enable bv-array-read))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; a variant for index n*k+i where i<k
(defthm bv-array-read-of-bvplus-of-bvmult-discard-vals
  (implies (and (syntaxp (and (quotep data)
                              (quotep k)
                              (quotep i)
                              (quotep index-width)
                              (quotep len)))
                (<= len (expt 2 index-width)) ; gen?? or other rules might help establish this
                (integerp len)
                (< i k)
                (< (+ i (* k index)) len) ; gen? the bvmult doesn't do any real chopping
                (integerp (/ len k)) ; gen? requires k to be a power of 2
                (< 1 k)
                (natp index)
                (natp i)
                (natp index-width)
                (integerp k))
           (equal (bv-array-read element-size len (bvplus index-width i (bvmult index-width k index)) data)
                  ;; The calls to nthcdr and every-nth get evaluated to give a smaller array:
                  (bv-array-read element-size (/ len k) index (every-nth k (nthcdr i data)))))
  :hints (("Goal" :in-theory (enable bv-array-read bvmult bvplus unsigned-byte-p))))

;; Discards the initial values in the array
(defthm bv-array-read-of-bvplus-of-constant-no-wrap
  (implies (and (syntaxp (and (quotep k)
                              (quotep data)
                              (quotep index-width)
                              (quotep len)))
                (< index (- (expt 2 index-width) k)) ; the bvplus does no chopping
                (< index (- len k)) ; the array access is in bounds
                (natp index-width)
                (natp k)
                (natp index))
           (equal (bv-array-read element-size len (bvplus index-width k index) data)
                  ;; The nthcdr here gets computed to give a smaller array:
                  (bv-array-read element-size (- len k) index (nthcdr k data))))
  :hints (("Goal" :in-theory (enable bv-array-read bvplus unsigned-byte-p))))
