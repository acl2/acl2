; Axe rules about BV arrays
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;this book uses the axe-syntaxp functions

;reduce?:
;(include-book "axe-syntax-functions") ;for SYNTACTIC-CALL-OF
(include-book "axe-syntax")
(include-book "axe-syntax-functions-bv")
(include-book "kestrel/bv-lists/bv-arrays" :dir :system)
(include-book "kestrel/bv/trim" :dir :system)
(include-book "kestrel/bv/bvlt" :dir :system)
(include-book "kestrel/booleans/boolor" :dir :system)
(include-book "kestrel/bv-lists/bv-arrayp" :dir :system)
(include-book "kestrel/bv/unsigned-byte-p-forced" :dir :system)
;(include-book "kestrel/bv/bvplus" :dir :system)
;(include-book "list-rules") ;for EQUAL-OF-UPDATE-NTH
(include-book "known-booleans")
(include-book "kestrel/lists-light/subrange" :dir :system)
;(local (include-book "kestrel/bv/bvlt" :dir :system))
(local (include-book "rules1"))
(local (include-book "list-rules")) ; for equal-of-update-nth
(local (include-book "kestrel/lists-light/update-nth" :dir :system))
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/lists-light/firstn" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
(local (include-book "kestrel/arithmetic-light/integer-length" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt2" :dir :system))

(add-known-boolean bv-arrayp)

;; Only needed for Axe
(defthmd integerp-of-bv-array-read
  (integerp (bv-array-read element-size len index data)))

;; Only needed for Axe
(defthmd natp-of-bv-array-read
  (natp (bv-array-read element-size len index data)))

;; Only needed for Axe
;bozo more like this?  gen the 0?
(defthmd bv-array-read-non-negative
  (not (< (bv-array-read esize len index data) 0)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;maybe not true?
;; (DEFTHM BV-ARRAY-WRITE-OF-BVCHOP-ARG4-better
;;   (IMPLIES (<= ELEMENT-SIZE SIZE)
;;            (EQUAL (BV-ARRAY-WRITE ELEMENT-SIZE
;;                                   LEN INDEX (BVCHOP SIZE VAL)
;;                                   DATA)
;;                   (BV-ARRAY-WRITE ELEMENT-SIZE LEN INDEX VAL DATA)))
;;   :hints (("Goal" :in-theory (enable BV-ARRAY-WRITE update-nth2)
;;            :cases ((integerp size)))))

;move
(defthmd bv-array-write-trim-value-all
  (implies (and (axe-syntaxp (term-should-be-trimmed-axe size val 'all dag-array))
                (natp len)
                (natp index)
                (< index len))
           (equal (bv-array-write size len index val array)
                  (bv-array-write size len index (trim size val)
                                  array)))
  :hints (("Goal" :in-theory (e/d (bv-array-write trim update-nth2)
                                  (;UPDATE-NTH-BECOMES-UPDATE-NTH2-EXTEND-GEN
                                   )))))

;move
(defthmd bv-array-write-trim-value
  (implies (and (axe-syntaxp (term-should-be-trimmed-axe size val 'non-arithmetic dag-array))
                (natp len)
                (natp index)
;                (integerp size) ;new
                (< index len))
           (equal (bv-array-write size len index val array)
                  (bv-array-write size len index (trim size val) array)))
  :hints (("Goal" :use (:instance bv-array-write-trim-value-all)
           :in-theory (disable bv-array-write-trim-value-all))))

(defthmd cons-becomes-bv-array-write-gen
  (implies (and (syntaxp (quotep data))
                (axe-bind-free (bind-bv-size-axe a 'newsize dag-array) '(newsize))
                (all-unsigned-byte-p newsize data) ;bozo what if not?
                (true-listp data)
                (natp newsize)
                (unsigned-byte-p-forced newsize a))
           (equal (cons a data)
                  (bv-array-write newsize (+ 1 (len data))
                                  0 a (cons 0 data))))
  :hints
  (("Goal" :in-theory (e/d (bv-array-write update-nth2 unsigned-byte-p-forced)
                           (;UPDATE-NTH-BECOMES-UPDATE-NTH2-EXTEND-GEN
                            )))))

(defthmd bv-array-write-of-bv-array-write-tighten2
  (implies (and (< element-size2 element-size1)
                (axe-bind-free (bind-bv-size-axe val1 'val-size dag-array) '(val-size))
                (<= val-size element-size2)
                (natp val-size)
                (< index1 len)
                (< index2 len)
                (equal len (len lst))
                (natp index1)
                (natp index2)
                (natp len)
                (natp element-size1)
                (natp element-size2)
                (unsigned-byte-p-forced val-size val1))
           (equal (bv-array-write element-size1 len index1 val1 (bv-array-write element-size2 len index2 val2 lst))
                  (bv-array-write element-size2 len index1 val1 (bv-array-write element-size2 len index2 val2 lst))))
  :hints (("Goal" :in-theory (e/d (update-nth2 len-update-nth BV-ARRAY-WRITE unsigned-byte-p-forced BVCHOP-LIST-OF-TAKE-OF-BVCHOP-LIST-GEN)
                                  (;UPDATE-NTH-BECOMES-UPDATE-NTH2-EXTEND-GEN
                                   )))))


(defthmd cons-of-bv-array-write-gen
  (implies (and (axe-bind-free (bind-bv-size-axe a 'asize dag-array) '(asize))
                (natp len)
                (< index len) ;Mon Jul 19 20:28:02 2010
                (natp esize)
                (natp asize)
                (natp index)
                (unsigned-byte-p-forced asize a))
           (equal (cons a (bv-array-write esize len index b lst))
                  (bv-array-write (max asize esize) (+ 1 len)
                                  0 a
                                  (bv-array-write esize (+ 1 len)
                                                  (+ 1 index)
                                                  b (cons a lst)))))
  :hints (("Goal" :in-theory (e/d (update-nth2 bv-array-write bvchop-of-sum-cases ceiling-of-lg
                                               ;;bvplus
                                               unsigned-byte-p-forced
                                               unsigned-byte-p
                                               equal-of-update-nth)
                                  (;bvplus-recollapse ;UPDATE-NTH-BECOMES-UPDATE-NTH2-EXTEND-GEN
                                   )))))

;; (defthmd bv-array-write-of-myif-drop-logext-lists-arg2
;;   (implies (and (axe-syntaxp (myif-nest-needs-bvchop-list x size dag-array)) ;else it could loop?
;;                 (natp index)
;;                 (< index len)
;;                 (natp len)
;;                 (posp size))
;;            (equal (bv-array-write size len index val (myif test y x))
;;                   (bv-array-write size len index val (myif test y (push-bvchop-list size x)))))
;;   :hints (("Goal" :in-theory (e/d (myif BV-ARRAY-WRITE update-nth2 bvchop-list-of-take-of-bvchop-list)
;;                                   (LIST::CLEAR-NTH-EQUAL-CLEAR-NTH-REWRITE
;;                                    UPDATE-NTH-BECOMES-UPDATE-NTH2-EXTEND-GEN)))))

;; (defthmd bv-array-write-of-myif-drop-logext-lists-arg1
;;   (implies (and (axe-syntaxp (myif-nest-needs-bvchop-list x size dag-array)) ;else it could loop?
;;                 (natp index)
;;                 (< index len)
;;                 (natp len)
;;                 (posp size))
;;            (equal (bv-array-write size len index val (myif test x y))
;;                   (bv-array-write size len index val (myif test (push-bvchop-list size x) y))))
;;   :hints (("Goal" :in-theory (e/d (myif BV-ARRAY-WRITE update-nth2 bvchop-list-of-take-of-bvchop-list)
;;                                   (LIST::CLEAR-NTH-EQUAL-CLEAR-NTH-REWRITE
;;                                    UPDATE-NTH-BECOMES-UPDATE-NTH2-EXTEND-GEN)))))

(defthmd myif-of-bv-array-write-arg1-safe
  (implies (and (axe-syntaxp (bv-array-write-nest-ending-inp-axe thenpart lst dag-array))
                (< key len)
                (all-unsigned-byte-p element-size thenpart) ;i guess we do need this...
                (natp key)
                (natp element-size)
                (true-listp thenpart)
                (equal len (len thenpart))  ;i guess we do need this...
                )
           (equal (myif test (bv-array-write element-size len key val lst) thenpart)
                  (bv-array-write element-size len key (myif test val (bv-array-read element-size len key thenpart)) (myif test lst thenpart))))
  :hints
  (("Goal"
    :in-theory (e/d (myif update-nth2 bv-array-read bv-array-write)
                    (nth-0-cons ;myif-of-constant-lists
                     NTH-OF-BV-ARRAY-WRITE-BECOMES-BV-ARRAY-READ ;UPDATE-NTH-BECOMES-UPDATE-NTH2-EXTEND-GEN
                     )))))

(defthmd myif-of-bv-array-write-arg2-safe
  (implies (and (axe-syntaxp (bv-array-write-nest-ending-inp-axe thenpart lst dag-array))
                (all-unsigned-byte-p element-size thenpart)
                (natp key)
                (equal len (len lst))
                (< key len)
                (natp element-size)
                (equal len (len thenpart))
                (true-listp thenpart))
           (equal (myif test thenpart (bv-array-write element-size len key val lst))
                  (bv-array-write element-size len key (myif test (bv-array-read element-size len key thenpart) val) (myif test thenpart lst))))
  :hints
  (("Goal"
    :in-theory (e/d (myif update-nth2 ;bv-array-read
                          bv-array-write
                          bv-array-read
                          )
                    (nth-0-cons ;myif-of-constant-lists
                     NTH-OF-BV-ARRAY-WRITE-BECOMES-BV-ARRAY-READ ;UPDATE-NTH-BECOMES-UPDATE-NTH2-EXTEND-GEN
                     )))))

;; (defthmd bv-array-read-of-myif-drop-logext-lists-arg2
;;   (implies (and (axe-syntaxp (myif-nest-needs-bvchop-list x size dag-array)) ;else it could loop?
;;                 (natp index)
;;                 (< index len)
;;                 (natp len)
;;                 (posp size))
;;            (equal (bv-array-read size len index (myif test y x))
;;                   (bv-array-read size len index (myif test y (push-bvchop-list size x)))))
;;   :hints (("Goal" :in-theory (enable myif BV-ARRAY-WRITE))))

;; (defthmd bv-array-read-of-myif-drop-logext-lists-arg1
;;   (implies (and (axe-syntaxp (myif-nest-needs-bvchop-list x size dag-array)) ;else it could loop?
;;                 (natp index)
;;                 (< index len)
;;                 (natp len)
;;                 (posp size))
;;            (equal (bv-array-read size len index (myif test x y))
;;                   (bv-array-read size len index (myif test (push-bvchop-list size x) y))))
;;   :hints (("Goal" :in-theory (enable myif BV-ARRAY-WRITE))))


(defthmd bv-array-write-tighten-when-quotep-data
  (implies (and (syntaxp (quotep array)) ;gen?
                (axe-bind-free (bind-bv-size-axe val 'valsize dag-array) '(valsize))
                (< valsize size) ;would loop if =
                (all-unsigned-byte-p valsize array)
                (natp size)
                (natp valsize)
                (natp index)
                (equal length (len array))
                (< index length) ;drop?
                (TRUE-LISTP ARRAY)
                (unsigned-byte-p-forced valsize val)
                )
           (equal (bv-array-write size length index val array)
                  (bv-array-write valsize length index val array)))
  :hints (("Goal" :in-theory (e/d (bv-array-write update-nth2 unsigned-byte-p-forced)
                                  (;UPDATE-NTH-BECOMES-UPDATE-NTH2-EXTEND-GEN
                                   )))))

(defthmd bv-array-write-does-nothing-cheap
  (implies (and (axe-syntaxp (bv-array-write-nest-with-val-at-indexp-axe lst val key dag-array)) ;this seemed very expensive in one situation (but it was because of huge bv-array-write nests due to some problem -- not this rule's fault)
                ;; this can be expensive, so we only do it when the test above indicates that it will succeed:
                (equal val (bv-array-read element-size len key lst))
                (equal len (len lst))
                (natp key)
                (< key (len lst)))
           (equal (bv-array-write element-size len key val lst)
                  (bvchop-list element-size lst)))
  :hints (("Goal" :in-theory (e/d (bv-array-write bv-array-read update-nth2
                                                  ;list::update-nth-equal-rewrite
                                                  BVCHOP-WHEN-I-IS-NOT-AN-INTEGER) ( ;take-of-bvchop-list
                                                  NTH-OF-BV-ARRAY-WRITE-BECOMES-BV-ARRAY-READ
                                                  ;;UPDATE-NTH-BECOMES-UPDATE-NTH2-EXTEND-GEN
                                                  )))))

(defthmd bv-array-read-trim-index-axe
  (implies (and (syntaxp (quotep len))
                (axe-binding-hyp (equal desired-size (ceiling-of-lg len))) ; binding hyp, desired-size should be a quoted constant
                (axe-syntaxp (term-should-be-trimmed-axe desired-size index 'non-arithmetic dag-array)))
           (equal (bv-array-read element-width len index data)
                  (bv-array-read element-width len (trim desired-size index) data)))
  :hints (("Goal" :in-theory (enable trim))))

(defthmd bv-array-read-trim-index-axe-all
  (implies (and (syntaxp (quotep len))
                (axe-binding-hyp (equal desired-size (ceiling-of-lg len))) ; desired-size should be a quoted constant
                (axe-syntaxp (term-should-be-trimmed-axe desired-size index 'all dag-array)))
           (equal (bv-array-read element-width len index data)
                  (bv-array-read element-width len (trim desired-size index) data)))
  :hints (("Goal" :use bv-array-read-trim-index-axe
           :in-theory (disable bv-array-read-trim-index-axe))))

;move
(defthmd myif-becomes-bv-array-if-axe
  (implies (and (axe-bind-free (bind-bv-array-length-axe x 'lenx dag-array) '(lenx))
                (axe-bind-free (bind-bv-array-length-axe y 'leny dag-array) '(leny))
                (axe-bind-free (bind-bv-array-element-size-axe x 'element-sizex dag-array) '(element-sizex))
                (axe-bind-free (bind-bv-array-element-size-axe y 'element-sizey dag-array) '(element-sizey))
                (equal element-sizex element-sizey) ;gen (take the larger?)
                (equal lenx leny)
                (bv-arrayp element-sizex lenx x) ;make a -forced version?
                (bv-arrayp element-sizey leny y) ;make a -forced version?
                )
           (equal (myif test x y)
                  (bv-array-if element-sizex lenx test x y)))
  :hints (("Goal" :in-theory (enable bv-array-if))))

;; todo: If val happens to be too narrow, we may need to widen the write later.
(defthmd update-nth-becomes-bv-array-write-axe
  (implies (and (axe-bind-free (bind-bv-size-axe val 'width dag-array) '(width))
                (all-unsigned-byte-p width lst)
                (unsigned-byte-p-forced width val)
                (< key (len lst))
                (natp key)
                (true-listp lst))
           (equal (update-nth key val lst)
                  (bv-array-write width (len lst) key val lst)))
  :hints (("Goal" :use update-nth-becomes-bv-array-write
           :in-theory (enable unsigned-byte-p-forced))))

;; Throws away array elements that can't be accessed (based on the size of the index term)
(defthmd bv-array-read-shorten-axe
  (implies (and (syntaxp (and (quotep len)
                              (quotep data)))
                (axe-bind-free (bind-bv-size-axe index 'isize dag-array) '(isize))
                (< (expt 2 isize) len) ; gets computed
                (equal len (len data)) ; gets computed
                (unsigned-byte-p-forced isize index))
           (equal (bv-array-read element-size len index data)
                  (bv-array-read element-size (expt 2 isize) index (take (expt 2 isize) data))))
  :hints (("Goal" :use (:instance bv-array-read-shorten-core)
           :in-theory (disable bv-array-read-shorten-core))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm bv-array-write-of-bv-array-write-diff-constant-indices-work-hard
  (implies (and (syntaxp (quotep index1))
                (syntaxp (quotep index2))
                (< index2 index1)
                (work-hard (< index1 len))
                (work-hard (< index2 len))
                (natp index1)
                (natp index2)
;                (work-hard (natp len)) ;drop?
                )
           (equal (bv-array-write element-size len index1 val1 (bv-array-write element-size len index2 val2 lst))
                  (bv-array-write element-size len index2 val2 (bv-array-write element-size len index1 val1 lst))))
  :hints (("Goal" :use (:instance bv-array-write-of-bv-array-write-diff-constant-indices)
           :in-theory (disable bv-array-write-of-bv-array-write-diff-constant-indices))))

(defthmd bv-array-read-of-bv-array-write-both-better-work-hard
  (implies (and (work-hard (< index1 len))
                (work-hard (< index2 len))
                (natp width2)
                (<= width width2)
                (integerp len)
                (natp index1)
                (natp index2))
           (equal (bv-array-read width len index1 (bv-array-write width2 len index2 val lst))
                  (if (not (equal index1 index2))
                      (bv-array-read width len index1 lst)
                    (bvchop width val))))
  :hints (("Goal" :use (:instance bv-array-read-of-bv-array-write-both-better)
           :in-theory (disable bv-array-read-of-bv-array-write-both-better))))

;this one has only one index, and so only one work-hard, so we will try this one first
(defthmd bv-array-read-of-bv-array-write-same-better-work-hard
  (implies (and (work-hard (< index len))
                (natp width2)
                (<= width width2)
                (integerp len)
                (natp index))
           (equal (bv-array-read width len index (bv-array-write width2 len index val lst))
                  (bvchop width val)))
  :hints (("Goal" :use (:instance bv-array-read-of-bv-array-write-both-better (index1 index) (index2 index))
           :in-theory (disable bv-array-read-of-bv-array-write-both-better))))

;todo: out of sync with the non-work-hard
(defthm bv-array-read-of-bv-array-write-same-work-hard
  (implies (and (natp index)
                (work-hard (< index len))
                (integerp len))
           (equal (bv-array-read width len index (bv-array-write width len index val lst))
                  (bvchop width val)))
  :hints (("Goal" :in-theory (enable bv-array-read-opener bv-array-write-opener))))

;TODO make non-work-hard versions of these
;includes both irrel cases
(defthm subrange-of-bv-array-write-irrel
  (implies (and (or (< high index)
                    (< index low))
                (< high len) ;handle?
                (work-hard (< index len))
                (natp len)
                (natp high)
                (natp index)
                (integerp low))
           (equal (subrange low high (bv-array-write width len index val data))
                  (subrange low high (bvchop-list width (take len data)))))
  :hints (("Goal" :in-theory (disable subrange))))

(defthm subrange-of-bv-array-write-in-range
  (implies (and (<= low index)  ;this case
                (<= index high) ;this case
                (work-hard (< high len)) ;work-hard is new
                (natp len)
                (natp high)
                (natp index)
                (natp low)
                )
           (equal (subrange low high (bv-array-write width len index val data))
                  (bv-array-write width (+ 1 high (- low)) (- index low) val (subrange low high data))))
  :hints (("Goal" :in-theory (e/d (bv-array-write-opener
                                   update-nth2
                                   subrange ;bozo?
                                   )
                                  (;anti-subrange
                                   ;CDR-OF-TAKE-BECOMES-SUBRANGE ;bozo
                                   UPDATE-NTH-BECOMES-UPDATE-NTH2-EXTEND-GEN)))))

;all cases - drop some hyps?
;this rule seemed to split into a lot of cases before the two "irrelevant write" cases were combined
(defthm subrange-of-bv-array-write
  (implies (and (work-hard (< index len))
                (work-hard (< high len)) ;drop?
                (natp len)
                (natp high)
                (natp index)
                (natp low)
                )
           (equal (subrange low high (bv-array-write width len index val data))
                  ;;recently combined the branches and made the or into a boolor
                  (if (boolor (< index low)
                              (< high index))
                      (subrange low high (bvchop-list width (take len data)))
                    (bv-array-write width (+ 1 high (- low)) (- index low) val (subrange low high data)))))
  :hints (("Goal" :in-theory (enable boolor))))

(defthmd cdr-of-bv-array-write-better-work-hard
  (implies (and (integerp len)
                (work-hard (< key len))
                (natp key))
           (equal (cdr (bv-array-write element-size len key val lst))
                  (if (zp len)
                      nil
                    (if (< key 1)
                        (bvchop-list element-size (cdr (take len (true-list-fix lst))))
                      (bv-array-write element-size (- len 1) (- key 1) val (nthcdr 1 lst))))))
  :hints (("Goal" :use (:instance cdr-of-bv-array-write-better)
           :in-theory (disable cdr-of-bv-array-write-better))))

;this version sets the length param of the bv-array-read to be the right
;todo: allow the lens in the lhs to differ?
(defthm bv-array-read-of-take-better
  (implies (and (posp len)
                (natp index)
                (work-hard (< index len))
                (<= len (len array)))
           (equal (bv-array-read elem-size len index (take len array))
                  (bv-array-read elem-size (len array) index array)))
  :hints (("Goal" :in-theory (e/d (bv-array-read-opener) ()))))

(defthmd bv-array-read-when-all-same-axe
  (implies (and (syntaxp (and (quotep data)
                              (quotep len) ;these prevent loops
                              (quotep element-size)))
                (axe-binding-hyp (equal val (bv-array-read element-size len 0 data))) ; should get computed
                (syntaxp (quotep val)) ; ensures the rule doesn't loop when the bv-array-read is not evaluated
                (all-equal$ val data);; should be evaluated
                (or (equal 0 val)  ;; if the array is all zeros, we don't need to show that the index is good
                    (and (natp index)
                         (< index len)))
                (equal (len data) len) ; should get computed
                )
           (equal (bv-array-read element-size len index data)
                  val))
  :hints (("Goal" :use bv-array-read-when-all-same
           :in-theory (disable bv-array-read-when-all-same))))
