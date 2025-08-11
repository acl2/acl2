; Reading a chunk of bytes from a bv-array
;
; Copyright (C) 2024-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/bv/bvcat-def" :dir :system)
(include-book "bv-array-read")
(include-book "unsigned-byte-listp")
(include-book "kestrel/utilities/defopeners" :dir :system)
(include-book "kestrel/utilities/def-constant-opener" :dir :system)
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
(local (include-book "kestrel/bv/unsigned-byte-p" :dir :system))
(local (include-book "kestrel/bv/bvcat" :dir :system))

;; From the ARRAY (described by ELEMENT-SIZE and ARRAY-LEN), read ELEMENT-COUNT
;; elements starting at INDEX and combine then into a single BV in a
;; little-endian way.
;; todo: inefficient? define in terms of packbv-little?
(defund bv-array-read-chunk-little (element-count element-size array-len index array)
  (declare (xargs :guard (and (natp element-size)
                              (unsigned-byte-listp element-size array)
                              (natp index)
                              (natp element-count)
                              (equal array-len (len array))
                              (< (+ -1 index element-count) array-len))))
  (if (zp element-count)
      0
    (bvcat (* element-size (+ -1 element-count))
           (bv-array-read-chunk-little (+ -1 element-count) element-size array-len (+ 1 index) array)
           element-size
           (bv-array-read element-size array-len index array))))

;; Discards irrelevant elements from the start of the array.
(defthm bv-array-read-chunk-little-of-+-arg4-when-constants
  (implies (and (syntaxp (and (quotep k)
                              (quotep array)))
                (natp index)
                (natp k)
                (equal array-len (len array))
                (< (+ -1 k index element-count) array-len))
           (equal (bv-array-read-chunk-little element-count element-size array-len (+ k index) array)
                  (bv-array-read-chunk-little element-count element-size (- array-len k) index (nthcdr k array))))
  :hints (("Goal" :in-theory (enable bv-array-read-chunk-little bv-array-read-opener))))

(defthm bv-array-read-chunk-little-of-+-of-expt-of-ceiling-of-lg
 (implies (and (natp len)
               (natp index))
          (equal (bv-array-read-chunk-little num element-width len (+ index (expt 2 (ceiling-of-lg len))) data)
                 (bv-array-read-chunk-little num element-width len index data)))
 :hints (("Goal" :in-theory (enable bv-array-read-chunk-little))))

(defthm bv-array-read-chunk-little-of-expt-of-ceiling-of-lg
 (implies (and (natp len)
               (natp index))
          (equal (bv-array-read-chunk-little num element-width len (expt 2 (ceiling-of-lg len)) data)
                 (bv-array-read-chunk-little num element-width len 0 data)))
 :hints (("Goal" :use (:instance bv-array-read-chunk-little-of-+-of-expt-of-ceiling-of-lg (index 0))
          :in-theory (disable bv-array-read-chunk-little-of-+-of-expt-of-ceiling-of-lg))))

;; we can usually unroll this into a bvcat if we can't do better
;; todo: try last?
(defopeners bv-array-read-chunk-little) ; do we want this if the index is not constant?
(def-constant-opener bv-array-read-chunk-little)

(defthm unsigned-byte-p-of-bv-array-read-chunk-little
  (implies (and (natp element-size)
                (natp element-count))
           (unsigned-byte-p (* element-size element-count)
                            (bv-array-read-chunk-little element-count element-size array-len index array)))
  :hints (("Goal" :in-theory (enable bv-array-read-chunk-little))))

(defthm unsigned-byte-p-of-bv-array-read-chunk-little-gen
  (implies (and (<= (* element-size element-count) size)
                (natp size)
                (natp element-size)
                (natp element-count))
           (unsigned-byte-p size (bv-array-read-chunk-little element-count element-size array-len index array)))
  :hints (("Goal" :use unsigned-byte-p-of-bv-array-read-chunk-little
           :in-theory (disable unsigned-byte-p-of-bv-array-read-chunk-little))))

;; (include-book "kestrel/bv/bvmult" :dir :system)
(include-book "packbvs-little")
;; (local (include-book "kestrel/arithmetic-light/times" :dir :system))
;; (local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/lists-light/reverse-list" :dir :system))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
;; (local (include-book "kestrel/arithmetic-light/plus-and-minus" :dir :system))
;; (local (include-book "kestrel/arithmetic-light/floor" :dir :system))
;; (local (include-book "packbv-theorems"))

;todo: use this for the :exec part of an mbe, or even for the main def!
(defthmd bv-array-read-chunk-little-alt-def
  (implies (and (posp element-count) ; gen?
                (posp element-size)                 ;(natp element-size)
                (unsigned-byte-listp element-size array)
                (natp index)
                (equal array-len (len array))
                ;(<= element-count array-len)
                (< (+ -1 index element-count) array-len))
           (equal (bv-array-read-chunk-little element-count element-size array-len index array)
                  (packbv-little element-count element-size (take element-count (nthcdr index array)))))
  :hints (("Goal" :induct t
           :in-theory (enable bv-array-read-chunk-little
                              packbv-little ; todo
                              packbv-opener-alt ;packbv
                              ))))

;; (thm
;;   (implies (and (posp element-count)
;;                 (posp element-size)
;;                 (unsigned-byte-listp element-size array)
;;                 (natp index)
;;                 (equal array-len (len array))
;;                 (<= element-count array-len))
;;            (equal (bv-array-read-chunk-little element-count element-size array-len 0 array)
;;                   (packbv-little element-count element-size (take element-count array))))
;;   :hints (("Goal" :induct t
;;            :in-theory (enable bv-array-read-chunk-little
;;                               packbv-little ; todo
;;                               ))))


;; ;; for example, reading a u32 from a list of bytes


;; (thm
;;   (implies (and (natp element-size)
;;                 (unsigned-byte-listp element-size array)
;;                 (natp index)
;;                 (natp element-count)
;;                 (equal array-len (len array))
;;                 (< (+ -1 index element-count) array-len)
;;                 (< 1 element-count)
;;                 (natp index-width)
;;                 (< (* element-count index) (expt 2 index-width)) ; no wrapping in the bvmult
;;                 (<= (expt 2 index-width) array-len)
;;                 (equal 0 (mod array-len element-count)) ;drop?
;;                 (equal element-count 4)
;;                 ;; (equal array-len 16)
;;                 (equal element-size 8)
;;                 ;; (equal index-width 4)
;;                 ;; (equal array '(0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15))
;;                 )
;;            (equal (bv-array-read-chunk-little element-count element-size array-len (bvmult index-width element-count index) array)
;;                   (bv-array-read-chunk-little 1 (* element-count element-size) (/ array-len element-count) index (packbvs-little element-count element-size array))))
;;   :hints (("Goal" ;; :induct (packbvs-little element-count element-size array)
;;            :induct t
;;            :in-theory (e/d (bv-array-read-chunk-little packbvs-little bvmult
;;                                                        bv-array-read
;;                                                        ) ((:i len)
;;                                                           bv-array-read-chunk-little-unroll expt)))))

;gen
(defthm bvchop-of-bv-array-read-chunk-little-same
  (implies (natp element-size)
           (equal (bvchop element-size (bv-array-read-chunk-little element-count element-size array-len index array))
                  (if (posp element-count)
                      (bv-array-read element-size array-len index array)
                    0))))
