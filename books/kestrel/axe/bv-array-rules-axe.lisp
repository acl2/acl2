; Axe rules about BV arrays
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;this book uses the axe-syntaxp functions

;reduce?:
(include-book "axe-syntax-functions") ;for SYNTACTIC-CALL-OF
(include-book "axe-syntax-functions-bv")
(include-book "kestrel/bv-lists/bv-arrays" :dir :system)
(include-book "kestrel/bv-lists/bv-arrayp" :dir :system)
(include-book "list-rules") ;for EQUAL-OF-UPDATE-NTH
(local (include-book "kestrel/lists-light/update-nth" :dir :system))
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/lists-light/firstn" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
(local (include-book "kestrel/arithmetic-light/integer-length" :dir :system))

(add-known-boolean bv-arrayp)

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
  :hints (("Goal" :in-theory (e/d (update-nth2 bv-array-write bvchop-of-sum-cases ceiling-of-lg bvplus unsigned-byte-p-forced)
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
  (implies (and (axe-syntaxp (bv-array-write-nest-ending-inp thenpart lst dag-array))
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
  (implies (and (axe-syntaxp (bv-array-write-nest-ending-inp thenpart lst dag-array))
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
  (implies (and (axe-syntaxp (bv-array-write-nest-with-val-at-index lst val key dag-array)) ;this seemed very expensive in one situation (but it was because of huge bv-array-write nests due to some problem -- not this rule's fault)
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

;gen!  may need a new syntax function
(defthmd bv-array-read-trim-index-dag-256
  (implies (and (axe-syntaxp (term-should-be-trimmed-axe '8 index 'non-arithmetic dag-array)) ;fixme had x here instead of index which caused a crash - check for that!
                ;(natp size)
                )
           (equal (bv-array-read element-width 256 index data)
                  (bv-array-read element-width 256 (trim 8 index) data)))
               :hints (("Goal" :in-theory (e/d (trim) nil))))

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
