; Reading a chunk of data from a BV list
;
; Copyright (C) 2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See also bv-array-read-chunk-little.
;; TODO: Adapt all rules about that one to apply to this one.

(include-book "kestrel/bv-lists/packbv-little" :dir :system)
(include-book "unsigned-byte-listp")
(include-book "kestrel/bv/bvplus" :dir :system)
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
(local (include-book "kestrel/lists-light/reverse-list" :dir :system))
;(local (include-book "kestrel/lists-light/cdr" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/bv/bvcat" :dir :system))
(local (include-book "kestrel/bv-lists/packbv-theorems" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))

(local (in-theory (disable len true-listp))) ; prevent induction

;move
;splits off the least significant chunk
(defthmd packbv-little-opener
  (implies (and (posp itemsize)
                (posp itemcount) ; for this opener
                (equal itemcount (len items)) ; drop? may need to redefine packbv-little
                ;(<= itemcount (len items))
                )
           (equal (packbv-little itemcount itemsize items)
                  (bvcat (* itemsize (+ -1 itemcount))
                         (packbv-little (+ -1 itemcount) itemsize (rest items))
                         itemsize
                         (first items))))
  :hints (("Goal"
           :in-theory (e/d (packbv-little
                            packbv-opener-alt-no-discard)
                           (distributivity)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Reads a chunk of data (a bit-vector) out of a list of bvs.
(defund bv-list-read-chunk-little (element-size
                                   element-count ; number of elements in the chunk
                                   index list)
  (declare (xargs :guard (and (natp element-size)
                              (natp element-count)
                              (unsigned-byte-listp element-size list)
                              (natp index)
                              (<= (+ index element-count)
                                  (len list)))))
  (packbv-little element-count element-size (take element-count (nthcdr index list))))

;; prevent matching a constant list?
(defthm bv-list-read-chunk-little-of-cons-irrel
  (implies (not (zp index))
           (equal (bv-list-read-chunk-little element-size element-count index (cons item list))
                  (bv-list-read-chunk-little element-size element-count (+ -1 index) list)))
  :hints (("Goal" :in-theory (enable bv-list-read-chunk-little))))

;; only do when index is 0?
(defthm bv-list-read-chunk-little-opener
  (implies (and (posp element-count) ; this rule
                (<= (+ index element-count) (len list))
                (posp element-size)
                (natp index))
           (equal (bv-list-read-chunk-little element-size element-count index list)
                  (bvcat (* element-size (+ -1 element-count))
                         (bv-list-read-chunk-little element-size (+ -1 element-count) (+ 1 index) list)
                         element-size
                         (nth index list))))
  :hints (("Goal" :cases ((posp (len items)))
           :in-theory (enable bv-list-read-chunk-little zp packbv-little-opener))))

(defthm bv-list-read-chunk-little-of-bvplus-of-constant
  (implies (and (syntaxp (and (quotep k)
                              (quotep list)))
                (< index (- (expt 2 size) k)) ; the bvplus does no chopping
;                (< index (- len k)) ; the array access is in bounds
                (natp size)
                (natp k)
                (natp index))
           (equal (bv-list-read-chunk-little element-size element-count (bvplus size k index) list)
                  (bv-list-read-chunk-little element-size element-count index (nthcdr k list))))
  :hints (("Goal" :in-theory (enable bv-list-read-chunk-little bvplus-becomes-+))))

;(local (include-book "kestrel/lists-light/take" :dir :system))
(defthmd bv-list-read-shorten-core
  (implies (and (<= (+ element-count index) bound)
                (natp index)
                (integerp bound)
                (natp element-count))
           (equal (bv-list-read-chunk-little element-size element-count index list)
                  (bv-list-read-chunk-little element-size element-count index (take bound list))))
  :hints (("Goal" :in-theory (enable bv-list-read-chunk-little))))

;;special case when index is a byte -- todo gen, using axe-syntaxp
(defthmd bv-list-read-shorten-core-8
  (implies (and (unsigned-byte-p 8 index)
                (natp element-count))
           (equal (bv-list-read-chunk-little element-size element-count index list)
                  (bv-list-read-chunk-little element-size element-count index (take (+ element-count -1 (expt 2 8)) list))))
  :hints (("Goal" :use (:instance acl2::bv-list-read-shorten-core (bound (+ 255 element-count)))
           :in-theory (enable unsigned-byte-p))))

;;special case when index is a byte -- todo gen, using axe-syntaxp
(defthmd bv-list-read-shorten-8
  (implies (and (syntaxp (and (quotep list)
                              (quotep element-count)))
                (unsigned-byte-p 8 index)
                (natp element-count))
           (equal (bv-list-read-chunk-little element-size element-count index list)
                  ;; the call of TAKE here should get evaluated:
                  (bv-list-read-chunk-little element-size element-count index (take (+ element-count -1 (expt 2 8)) list))))
  :hints (("Goal" :use (:instance acl2::bv-list-read-shorten-core (bound (+ 255 element-count)))
           :in-theory (enable unsigned-byte-p))))
