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
(include-book "map-bvsx")
(include-book "map-bvplus-val")
(include-book "kestrel/bv/bvmult" :dir :system)
(include-book "kestrel/bv/bvplus" :dir :system)
(include-book "kestrel/bv/bvcat" :dir :system)
(include-book "kestrel/bv/bvlt" :dir :system)
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
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/revappend" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/take" :dir :system))

(local (in-theory (disable take)))

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
                ;; todo: should these use bvlt?
                (< index (/ (expt 2 index-width) k)) ; the bvmult doesn't do any real chopping ; gen in the power-of-2 case?
                (< index (/ len k)) ; (bvlt index-width index (/ len k))  ; the access is in bounds
                (< 1 k) ; prevents loops
                (<= len (len data)) ; drop?
                (integerp len)
                (natp index)
                (natp index-width)
                (integerp k))
           (equal (bv-array-read element-size len (bvmult index-width k index) data)
                  ;; The call to every-nth gets evaluated:
                  (let ((data (every-nth k data)))
                    (bv-array-read element-size (len data) index data))))
  :hints (("Goal" :in-theory (enable bv-array-read bvmult unsigned-byte-p bvlt bvchop-identity))))

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

(local
 (defthmd bv-array-read-of-bvplus-of-constant-no-wrap-bv-helper
   (implies (and (syntaxp (and (quotep k)
                               (quotep data)
                               (quotep index-width)
                               (quotep len)))
                 (equal index-width (ceiling-of-lg len))
                 (bvlt index-width index (bvplus index-width index k)) ; no wrap around
                 ;;(bvlt (+ 1 index-width) (bvplus (+ 1 index-width) index k) len) ; in bounds (uses index-width+1 bit because len might be a power of 2)
                 (or (power-of-2p len)
                     (bvlt index-width (bvplus index-width index k) len))
                 (unsigned-byte-p index-width index) ; todo
                 (unsigned-byte-p index-width k)     ; todo
                 (natp index-width)
                 (natp k)
                 (natp len)
                 (natp index))
            (equal (bv-array-read element-size len (bvplus index-width k index) data)
                   ;; The nthcdr here gets computed to give a smaller array:
                   (bv-array-read element-size (bvminus index-width len k) index (nthcdr k data))))
   :hints (("Goal" :use (:instance bv-array-read-of-bvplus-of-constant-no-wrap
                                   (index-width (ceiling-of-lg len))
                                   )
                   :in-theory (e/d (bvlt bvplus bvchop-of-sum-cases bvminus)
                                   (bv-array-read-of-bvplus-of-constant-no-wrap))))))

(defthmd bv-array-read-of-bvplus-of-constant-no-wrap-bv
  (implies (and (syntaxp (and (quotep k)
                              (quotep data)
                              (quotep index-width)
                              (quotep len)))
                (equal index-width (ceiling-of-lg len))               ; gen?
                (bvlt index-width index (bvplus index-width index k)) ; no wrap around
                (or (power-of-2p len)
                    (bvlt index-width (bvplus index-width index k) len)) ; in bounds
                ;; (natp index-width)
                ;; (natp k)
                (natp len)
                ;; (natp index)
                )
           (equal (bv-array-read element-size len (bvplus index-width k index) data)
                  ;; The nthcdr here gets computed to give a smaller array:
                  (bv-array-read element-size (bvminus index-width len k) (bvchop index-width index) (nthcdr (bvchop index-width k) data))))
  :hints (("Goal" :use (:instance bv-array-read-of-bvplus-of-constant-no-wrap-bv-helper
                                  (index (bvchop index-width index))
                                  (k (bvchop index-width k))))))


;yuck?
;needed for the below
;disable?
(defthm equal-of-bv-array-read-and-bv-array-read-lens-differ
  (implies (and (< index len1)
                (< index len2)
                (natp len1)
                (natp len2)
                (natp index)
                )
           (equal (equal (bv-array-read width len1 index data) (bv-array-read width len2 index data))
                  t))
  :hints (("Goal" :cases ((< len1 len2))
           :in-theory (enable bv-array-read-opener))))

(local
  (defthmd bv-array-read-shorten-when-bvlt-gen-helper
    (implies (and (unsigned-byte-p (ceiling-of-lg len) index) ; for the helper
                  (syntaxp (and (quotep data)
                                (quotep len)))
                  (bvlt size2 index k) ; index < k, k is a free var
                  (equal size2 (ceiling-of-lg len)) ; gen?
                  (syntaxp (quotep k))
                  (< k len) ; avoid loops (gets evaluated)
                  (natp k)
                  (natp len))
             (equal (bv-array-read element-size len index data)
                    (bv-array-read element-size k index (take k data))))
    :hints (("Goal" :cases ((equal (bvchop (ceiling-of-lg k) index)
                                   (bvchop (ceiling-of-lg len) index)))
             :in-theory (e/d (bvlt bv-array-read)
                             (equal-of-bvchop-and-bvchop-same))))))

;; When the index is < k, we discard all but the first k array elements,
;; because later elements cannot be accessed.
;; todo: make a <= (bvle) version
(defthmd bv-array-read-shorten-when-bvlt-gen
  (implies (and (syntaxp (and (quotep data)
                              (quotep len)))
                (bvlt size2 index k) ; index < k, k is a free var
                (equal size2 (ceiling-of-lg len)) ; gen?
                (syntaxp (quotep k))
                (< k len) ; avoid loops (gets evaluated)
                (natp k)
                (natp len))
           (equal (bv-array-read element-size len index data)
                  (bv-array-read element-size k index (take k data))))
  :hints (("Goal" :use (:instance bv-array-read-shorten-when-bvlt-gen-helper
                                  (index (bvchop (ceiling-of-lg len) index))))))

;; here we guess that the index may be < ~half the array size.  if so, we can
;; discard the latter ~half of the values.
(defthmd bv-array-read-shorten-when-in-first-half
  (implies (and (syntaxp (and (quotep data)
                              (quotep len)))
                (bvlt (ceiling-of-lg len) index (ceiling len 2))
                (< (ceiling len 2) len) ; avoid loops (gets evaluated) ; todo: simplify
                (natp len))
           (equal (bv-array-read element-size len index data)
                  (bv-array-read element-size (ceiling len 2) index (take (ceiling len 2) data))))
  :hints (("Goal" :use (:instance bv-array-read-shorten-when-bvlt-gen
                                  (size2 (ceiling-of-lg len))
                                  (k (ceiling len 2))))))

;; When the index is < k, we discard all but the first k array elements,
;; because later elements cannot be accessed.
; compare to the gen one above
(defthmd bv-array-read-shorten-when-bvlt
  (implies (and (syntaxp (and (quotep data)
                              (quotep len)))
                (bvlt isize index k) ; k is a free var
                (syntaxp (and (quotep k)
                              (quotep isize)))
                (< k len) ; avoid loops
                (< k (expt 2 isize)) ; so the chop on k goes away
                (natp k)
                (natp len))
           (equal (bv-array-read element-size len (bvchop isize index) data)
                  (bv-array-read element-size k (bvchop isize index) (take k data))))
  :hints (("Goal" :in-theory (enable bvlt <=-of-bvchop-same-linear))))

;; When the index is <= k, we discard all but the first k+1 array elements,
;; because later elements cannot be accessed.
(defthmd bv-array-read-shorten-when-not-bvlt ; could rename to say -when-bvle
  (implies (and (syntaxp (and (quotep data)
                              (quotep len)))
                (not (bvlt isize k index)) ; k is a free var
                (syntaxp (and (quotep k)
                              (quotep isize)))
                (< (+ 1 k) len) ; avoid loops
                (< (+ 1 k) (expt 2 isize)) ; so the chop on k goes away
                (natp index)
                (natp k)
                (natp len))
           (equal (bv-array-read element-size len (bvchop isize index) data)
                  (bv-array-read element-size (+ 1 k) (bvchop isize index) (take (+ 1 k) data))))
  :hints (("Goal" :in-theory (e/d (bvlt <=-of-bvchop-same-linear)
                                  (bv-array-read-of-cons-both)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defthm <-when-power-of-2p-and-unsigned-byte-p
   (implies (and (power-of-2p len)
                 (unsigned-byte-p (ceiling-of-lg len)
                                  index))
            (< index len))
   :hints (("Goal" :in-theory (enable unsigned-byte-p)))))

(defthmd bv-array-read-shorten-when-not-bvlt-gen
  (implies (and (syntaxp (and (quotep data)
                              (quotep len)))
                (bvle size2 k index) ; index > k, k is a free var
                (or (power-of-2p len) ; in this case, the index is in bounds because it is an unsigned-byte
                    (bvlt (ceiling-of-lg len) index len))
                (equal size2 (ceiling-of-lg len)) ; gen?
                (syntaxp (quotep k))
                (unsigned-byte-p size2 k)     ; gen?
                (unsigned-byte-p size2 index) ; gen?
                ;;(<= 1 k) ; prevents loops
                (natp k)
                (natp len))
           (equal (bv-array-read element-size len index data)
                  (bv-array-read element-size (- len k) (- index k) (nthcdr k data))))
  :hints (("Goal" :in-theory (enable bv-array-read bvlt bvchop-of-sum-cases))))

(local (include-book "kestrel/arithmetic-light/floor" :dir :system))

(local
 (defthm unsigned-byte-p-of-ceiling-of-lg-and-ceiling-of-2
   (implies (and (< 1 i)
                 (integerp i))
            (unsigned-byte-p (ceiling-of-lg i) (ceiling i 2)))
   :hints (("Goal" :in-theory (enable unsigned-byte-p)))))

(local
 (defthm +-of---of-ceiling-of-2-same
   (implies (and (power-of-2p i)
                 (< 1 i))
            (equal (+ i (- (ceiling i 2)))
                   (ceiling i 2)))
   :hints (("Goal" :in-theory (enable power-of-2p)))))

;; todo:  (<= (floor i 2) 1)

;; (thm
;;  (implies (and (posp i)
;;                (< 1 i))
;;           (equal (integer-length (ceiling i 2))
;;                  (+ -1 (integer-length i))))
;;  :hints (("Goal" :in-theory (enable ceiling-in-terms-of-floor-cases))))

(local
 (defthm integer-length-of-ceiling-of-2-when-power-of-2p
   (implies (and (power-of-2p i) ; drop?
                 (integerp i))
            (equal (integer-length (ceiling i 2))
                   (if (< 1 i)
                       (+ -1 (integer-length i))
                     1)))
   :hints (("Goal" :in-theory (enable ceiling-in-terms-of-floor-cases
                                      floor-when-evenp)))))

(local
 (defthm power-of-2p-of-ceiling-of-2
   (implies (power-of-2p i)
            (power-of-2p (ceiling i 2)))
   :hints (("Goal" :in-theory (enable power-of-2p expt-of-+)))))

(local
 (defthm hhelper
   (equal (+ len (- (* 1/2 len)))
          (* 1/2 len))))

;; This discards the first ~half of the array values, but it does complicate
;; the index term by subtracting a constant from it.
(defthmd bv-array-read-shorten-when-in-second-half
  (implies (and (syntaxp (and (quotep data)
                              (quotep len)))
                (integerp len) ; prevent loops, because (ceiling-of-lg len) is at least 1, so the length decreases
                (< 1 len)  ; seems needed
                (bvle (ceiling-of-lg len) (ceiling len 2) index) ; index in second half
                ;; index in bounds:
                (or (power-of-2p len) ; in this case, the (chopped) index is always in bounds
                    (bvlt (ceiling-of-lg len) index len))
                (integerp index))
           (equal (bv-array-read element-size len index data)
                  (bv-array-read element-size
                                 (- len (ceiling len 2)) ; gets computed
                                 (bvminus (ceiling-of-lg len) index (ceiling len 2))
                                 (nthcdr (ceiling len 2) data))))
  :hints (("Goal" :expand ((bvplus (ceiling-of-lg len)
                                   index
                                   (bvuminus (ceiling-of-lg len)
                                             (ceiling len 2)))
                           (bvuminus (ceiling-of-lg len)
                                     (ceiling len 2)))
                   :in-theory (e/d (bvuminus bvplus) (;ceiling-when-multiple
                                                     ))
                  :use (:instance bv-array-read-shorten-when-not-bvlt-gen
                                  (k (ceiling len 2))
                                  (size2 (ceiling-of-lg len))
                                  (index (bvchop (ceiling-of-lg len) index))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm bvsx-of-bv-array-read-constant-array
  (implies (and (syntaxp (quotep data))
                (equal len (len data))
                (natp new-size)
                (natp old-size))
           (equal (bvsx new-size old-size (bv-array-read old-size len index data))
                  (bv-array-read new-size len index (map-bvsx new-size old-size data))))
  :hints (("Goal" :in-theory (enable bv-array-read bvsx-of-nth))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm bvplus-of-bv-array-read-constant-array
  (implies (and (syntaxp (and (quotep data)
                              (quotep val)
                              (quotep size)))
                (natp size)
                (or (power-of-2p len)
                    (bvlt (ceiling-of-lg len) index (len data)))
                (equal len (len data)))
           (equal (bvplus size val (bv-array-read size len index data))
                  (bv-array-read size len index (map-bvplus-val size val data))))
  :hints (("Goal" :in-theory (enable bv-array-read acl2::bvplus-of-nth bvlt))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Splitting an array-read into cases based on the index:

(defund bv-array-read-cases (i size len index data)
  (if (zp i)
      (bv-array-read size len 0 data)
    (if (equal i (bvchop (ceiling-of-lg len) index))
        (bv-array-read size len i data)
      (bv-array-read-cases (+ -1 i) size len index data))))

;(defopeners bv-array-read-cases) ; didn't work well (rules too specific?)
(defthm bv-array-read-cases-opener
  (implies (syntaxp (quotep i))
           (equal (bv-array-read-cases i size len index data)
                  (if (zp i)
                      (bv-array-read size len 0 data)
                    (if (equal i (bvchop (ceiling-of-lg len) index))
                        (bv-array-read size len i data)
                      (bv-array-read-cases (+ -1 i) size len index data)))))
  :hints (("Goal" :in-theory (enable bv-array-read-cases))))

(local
 (defthm helper
   (implies (and (not (equal 0 i))
                 (not (equal i (bvchop size index)))
                 (not (bvlt size i index))
                 (natp index)
                 (unsigned-byte-p size i)
                 )
            (not (bvlt size (bvplus size -1 i) index)))
   :hints (("Goal" :do-not-induct t :in-theory (enable bvlt bvplus)))))

(local
 (defthmd bv-array-read-becomes-bv-array-read-cases-helper
   (implies (and (bvle (ceiling-of-lg len) index i)
                 (natp index)
                 (unsigned-byte-p (ceiling-of-lg len) i)
                 (natp i))
            (equal (bv-array-read size len index data)
                   (bv-array-read-cases i size len index data)))
   :hints (("Goal" :induct (bv-array-read-cases i size len index data)
                   :expand ((bv-array-read size len 0 data)
                            (bv-array-read size len index data))
                   :in-theory (enable bv-array-read-cases
                                      bvlt
                                      ;;acl2::bvlt-convert-arg2-to-bv
                                      ;;acl2::trim-of-+-becomes-bvplus ; don't we want this enabled?
                                      )))))

;; restrict to constant array?
(defthmd bv-array-read-becomes-bv-array-read-cases
  (implies (and (posp len)
                (natp index)
                (unsigned-byte-p (ceiling-of-lg len) index)
                (bvle (ceiling-of-lg len) index (+ -1 len)) ; todo?
                )
           (equal (bv-array-read size len index data)
                  (bv-array-read-cases (bvchop (ceiling-of-lg len) (+ -1 len))
                                       size len index data)))
  :hints (("Goal" :use (:instance bv-array-read-becomes-bv-array-read-cases-helper
                                  (i (+ -1 len))))))
