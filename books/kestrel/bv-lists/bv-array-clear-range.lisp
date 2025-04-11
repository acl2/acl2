; Clearing ranges of values in bv-arrays
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "bv-array-clear")
(include-book "kestrel/lists-light/all-equal-dollar" :dir :system)
(local (include-book "all-unsigned-byte-p2"))
(local (include-book "kestrel/arithmetic-light/integer-length" :dir :system))
(local (include-book "kestrel/lists-light/update-nth" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/lists-light/take2" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
(local (include-book "kestrel/lists-light/cons" :dir :system))
(local (include-book "kestrel/lists-light/all-equal-dollar2" :dir :system)) ;for ALL-EQUAL$-WHEN-TRUE-LISTP

(defund bv-array-clear-range (esize len lowindex highindex data)
  (declare (xargs :measure (+ 1 (nfix (+ 1 (- highindex lowindex))))
                  :guard (and (true-listp data)
                              (all-integerp data)
                              (natp len)
                              (<= LEN (LEN DATA))
                              (natp esize)
                              (rationalp highindex)
                              (rationalp lowindex)
                              (< highindex len))
                  :verify-guards nil ;done below
                  ))
  (if (or (not (natp highindex))
          (not (natp lowindex))
          (> lowindex highindex))
      (bvchop-list esize (take len data)) ;was data
    (bv-array-clear esize len lowindex (bv-array-clear-range esize len (+ 1 lowindex) highindex data))))

(defthm bv-array-clear-range-of-true-list-fix
  (implies (and (<= lowindex highindex)
                (natp lowindex)
                (natp highindex))
           (equal (bv-array-clear-range elem-size len lowindex highindex (true-list-fix lst))
                  (bv-array-clear-range elem-size len lowindex highindex lst)))
  :hints (("Goal" :in-theory (enable bv-array-clear-range))))

(defthm nth-of-bv-array-clear-range
  (implies (and (natp len)
                (natp n)
                (natp lowindex)
                (natp highindex)
                (<= lowindex n)
                (<= n highindex)
                (<= lowindex highindex)
                (< highindex len)
                )
           (equal (nth n (bv-array-clear-range elem-size len lowindex highindex lst))
                  0))
  :hints (("Goal" :in-theory (enable bv-array-clear-range bv-array-write update-nth2))))

;; (thm
;;  (equal (BV-ARRAY-CLEAR ELEM-SIZE len len LST)
;;         (BVCHOP-LIST ELEM-SIZE (TAKE LEN LST)))
;;  :hints (("Goal" :in-theory (enable BV-ARRAY-CLEAR bv-array-write update-nth2))))

;; (thm
;;  (equal (BV-ARRAY-CLEAR-RANGE ELEM-SIZE len len HIGHINDEX LST)
;;         (BVCHOP-LIST ELEM-SIZE (TAKE LEN LST)))
;;  :hints (("Goal" :in-theory (enable BV-ARRAY-CLEAR-RANGE))))

(defthm nth-of-bv-array-clear-range-low
  (implies (and (< n lowindex)
                (< lowindex len)
                (natp len)
                (natp n)
                (natp lowindex)
        ;        (equal len (len lst))
                (natp highindex)
                (<= lowindex highindex)
                (< highindex len))
           (equal (nth n (bv-array-clear-range elem-size len lowindex highindex lst))
                  (bvchop elem-size (nth n lst))))
  :hints (("Goal" :in-theory (enable bv-array-clear-range bv-array-write update-nth2))))

(defthm len-of-bv-array-clear-range
  (equal (len (bv-array-clear-range esize len lowindex highindex data))
         (nfix len))
  :hints (("Goal" :in-theory (enable bv-array-clear-range))))

(defthm all-integerp-of-bv-array-clear-range
  (all-integerp (bv-array-clear-range esize len lowindex highindex data))
  :hints (("Goal" :in-theory (enable bv-array-clear-range))))

(verify-guards bv-array-clear-range :hints (("Goal" :do-not-induct t)))

;; disabled since ACL2 knows this by type reasoning
(defthmd true-listp-of-bv-array-clear-range
  (true-listp (bv-array-clear-range elem-size len lowindex highindex lst)))

(defthm bv-array-clear-range-of-repeat-same
  (equal (bv-array-clear-range '8 len start end (repeat len 0))
         (repeat len 0))
  :hints (("Goal" :cases ((natp len))
           :in-theory (enable bv-array-clear-range))))

;restrict to constants?
(defthm bv-array-clear-range-of-zeros
  (implies (and (all-equal$ 0 data)
                (true-listp data)
                (equal len (len data)))
           (equal (bv-array-clear-range '8 len start end data)
                  data))
  :hints (("Goal" :use bv-array-clear-range-of-repeat-same
           :in-theory (e/d (ALL-EQUAL$-WHEN-TRUE-LISTP)
                           (bv-array-clear-range-of-repeat-same
                            equal-of-repeat-of-len-same)))))

(defthm bv-array-clear-range-when-out-of-order
  (implies (< highindex lowindex)
           (equal (bv-array-clear-range esize len lowindex highindex data)
                  (bvchop-list esize (take len data))))
  :hints (("Goal" :in-theory (enable bv-array-clear-range))))

;; no, the index gets chopped?
;; (defthm bv-array-clear-range-when-low-too-high
;;   (implies (<= len lowindex)
;;            (equal (bv-array-clear-range esize len lowindex highindex data)
;;                   (bvchop-list esize (take len data))))
;;   :hints (("Goal" :in-theory (enable bv-array-clear-range))))

(defthm bv-array-clear-of-bv-array-clear-adjacent1
  (implies (and (equal index2 (+ 1 index1))
                (< index1 len)
                (< index2 len)
                (natp elem-size)
                (natp len)
                (natp index1)
                (natp index2))
           (equal (bv-array-clear elem-size len index1 (bv-array-clear elem-size len index2 lst))
                  (bv-array-clear-range elem-size len index1 index2 lst)))
  :hints (("Goal" :in-theory (enable bv-array-clear-range))))

(defthm bv-array-clear-of-bv-array-clear-adjacent2
  (implies (and (equal index1 (+ 1 index2))
                (< index1 len)
                (< index2 len)
                (natp elem-size)
                (natp len)
                (natp index1)
                (natp index2))
           (equal (bv-array-clear elem-size len index1 (bv-array-clear elem-size len index2 lst))
                  (bv-array-clear-range elem-size len index2 index1 lst))))

(defthm bv-array-clear-of-bv-array-clear-range-adjacent1
  (implies (and (equal lowindex (+ 1 index1))
                (< index1 len)
                (< lowindex len)
                (< highindex len)
                (<= lowindex highindex)
                (natp elem-size)
                (natp len)
                (natp index1)
                (natp lowindex)
                (natp highindex))
           (equal (bv-array-clear elem-size len index1 (bv-array-clear-range elem-size len lowindex highindex lst))
                  (bv-array-clear-range elem-size len index1 highindex lst)))
  :hints (("Goal" :in-theory (enable bv-array-clear-range))))

(defthm bv-array-clear-of-bv-array-clear-range-adjacent2
  (implies (and (equal index1 (+ 1 highindex))
                (< index1 len)
                (< lowindex len)
                (< highindex len)
                (<= lowindex highindex)
                (natp elem-size)
                (natp len)
                (natp index1)
                (natp lowindex)
                (natp highindex))
           (equal (bv-array-clear elem-size len index1 (bv-array-clear-range elem-size len lowindex highindex lst))
                  (bv-array-clear-range elem-size len lowindex index1 lst)))
  :hints (("Goal" :in-theory (enable bv-array-clear-range))))

(defthm bv-array-clear-range-of-bv-array-clear
  (implies (and (< index1 len)
                (< lowindex len)
                (< highindex len)
                (<= lowindex highindex)
                (natp elem-size)
                (natp len)
                (natp index1)
                (natp lowindex)
                (natp highindex))
           (equal (bv-array-clear-range elem-size len lowindex highindex (bv-array-clear elem-size len index1 lst))
                  (bv-array-clear elem-size len index1 (bv-array-clear-range elem-size len lowindex highindex lst))))
  :hints (("Goal" :in-theory (enable bv-array-clear-range))))

(defthm bv-array-clear-range-of-bv-array-clear-adjacent1
  (implies (and (equal lowindex (+ 1 index1))
                (< index1 len)
                (< lowindex len)
                (< highindex len)
                (<= lowindex highindex)
                (natp elem-size)
                (natp len)
                (natp index1)
                (natp lowindex)
                (natp highindex))
           (equal (bv-array-clear-range elem-size len lowindex highindex (bv-array-clear elem-size len index1 lst))
                  (bv-array-clear-range elem-size len index1 highindex lst)))
  :hints (("Goal" :in-theory (e/d (bv-array-clear-range) (bv-array-clear-of-bv-array-clear-range-adjacent1 bv-array-clear-of-bv-array-clear-range-adjacent2)))))

(defthm bv-array-clear-range-of-bv-array-clear-adjacent2
  (implies (and (equal index1 (+ 1 highindex))
                (< index1 len)
                (< lowindex len)
                (< highindex len)
                (<= lowindex highindex)
                (natp elem-size)
                (natp len)
                (natp index1)
                (natp lowindex)
                (natp highindex))
           (equal (bv-array-clear-range elem-size len lowindex highindex (bv-array-clear elem-size len index1 lst))
                  (bv-array-clear-range elem-size len lowindex index1 lst))))

(defthm bv-array-clear-range-same
  (implies (natp key)
           (equal (bv-array-clear-range esize len key key lst)
                  (bv-array-clear esize len key lst)))
  :hints (("Goal" :expand ((bv-array-clear-range esize len key key lst)))))

;gross to mix theories?


(defthm nth-of-bv-array-clear-range-contained
  (implies (and (<= low index)
                (<= index high)
                (< high len)
                (natp low)
                (natp len)
                (natp high)
                (natp index))
           (equal (nth index (bv-array-clear-range size len low high data))
                  0))
  :hints (("Goal" :in-theory (enable bv-array-clear-range
                                     bv-array-clear))))

;; (DEFTHM BV-ARRAY-CLEAR-OF-BV-ARRAY-CLEAR-DIFF-gen
;;   (IMPLIES
;;    (AND (SYNTAXP (SMALLER-TERMP INDEX2 INDEX1))
;;         (<= ELEMENT-SIZE2 ELEMENT-SIZE1)
;; ;        (< INDEX1 LEN)
;;  ;       (< INDEX2 LEN)
;;         (NATP INDEX1)
;;         (NATP INDEX2)
;;         (NATP LEN)
;;         (NATP ELEMENT-SIZE1)
;;         (NATP ELEMENT-SIZE2))
;;    (EQUAL (BV-ARRAY-CLEAR
;;            ELEMENT-SIZE1 LEN INDEX1
;;            (BV-ARRAY-CLEAR ELEMENT-SIZE2 LEN INDEX2 LST))
;;           (BV-ARRAY-CLEAR
;;            ELEMENT-SIZE2 LEN INDEX2
;;            (BV-ARRAY-CLEAR ELEMENT-SIZE2 LEN INDEX1 LST))))
;;   :hints (("Goal" :use (:instance BV-ARRAY-CLEAR-OF-BV-ARRAY-CLEAR-DIFF)
;;            :in-theory (e/d (BV-ARRAY-CLEAR)
;;                            ( BV-ARRAY-CLEAR-OF-BV-ARRAY-CLEAR-DIFF)))))

;todo: prove from the other one?
(defthmd bv-array-clear-of-bv-array-clear-range
  (implies (and (< index len)
                (< high len)
                (< low len)
                (natp len)
                (natp low)
                (natp high)
                (natp size)
                (natp index))
           (equal (bv-array-clear size len index (bv-array-clear-range size len low high data))
                  (bv-array-clear-range size len low high (bv-array-clear size len index data))))
  :hints (("Goal"
           ;;:induct (clear-ind index high data)
           :induct t
           :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (bv-array-clear-range)
                           (;bv-array-clear-range-same
                            ;update-nth-becomes-update-nth2-extend-gen
                            )))))

(theory-invariant (incompatible (:rewrite bv-array-clear-of-bv-array-clear-range) (:rewrite bv-array-clear-range-of-bv-array-clear)))

;todo: drop now?
;; (defthm bv-array-clear-of-bv-array-clear-range
;;   (implies (and (natp len)
;;                 (< LOWINDEX LEN)
;;                 (< INDEX LEN)
;;                 (natp index)
;;                 (natp elemement-width))
;;            (equal (bv-array-clear elemement-width len index (bv-array-clear-range elemement-width len lowindex highindex data))
;;                   (bv-array-clear-range elemement-width len lowindex highindex (bv-array-clear elemement-width len index data))))
;;   :hints (("Goal" :in-theory (enable bv-array-clear-range))))

(defthm bv-array-clear-range-of-bv-array-write-contained
  (implies (and (<= low index)
                (<= index high)
                (< high len)
                (equal len (len data))
                (natp len)
                (natp low)
                (natp high)
                (natp size)
                (natp index))
           (equal (bv-array-clear-range size len low high (bv-array-write size len index val data))
                  (bv-array-clear-range size len low high data)))
  :hints (("Subgoal *1/2" :cases ((< high (+ 1 index))))
          ("Goal"
;:induct (clear-ind index high data)
           :induct t
           :do-not '(generalize eliminate-destructors)
           :expand ((BV-ARRAY-CLEAR-RANGE SIZE (LEN DATA)
                                          LOW HIGH
                                          (BV-ARRAY-WRITE SIZE (LEN DATA)
                                                          HIGH VAL DATA))
                    (BV-ARRAY-CLEAR-RANGE SIZE (LEN DATA)
                                          (+ 1 HIGH)
                                          HIGH
                                          (BV-ARRAY-WRITE SIZE (LEN DATA)
                                                          HIGH VAL DATA))
                    (BV-ARRAY-CLEAR-RANGE SIZE (LEN DATA)
                                          HIGH HIGH
                                          (BV-ARRAY-WRITE SIZE (LEN DATA)
                                                          HIGH VAL DATA))
                    (BV-ARRAY-CLEAR-RANGE SIZE (LEN DATA)
                                          (+ 1 HIGH)
                                          HIGH DATA)
                    (BV-ARRAY-CLEAR-RANGE SIZE (LEN DATA)
                                          LOW HIGH DATA)
                    (BV-ARRAY-CLEAR-RANGE SIZE (LEN DATA)
                                          LOW HIGH
                                          (BV-ARRAY-WRITE SIZE (LEN DATA)
                                                          INDEX VAL DATA))
                    (BV-ARRAY-CLEAR-RANGE SIZE (LEN DATA)
                                          INDEX HIGH DATA)
                    (BV-ARRAY-CLEAR-RANGE SIZE (LEN DATA)
                                          INDEX HIGH
                                          (BV-ARRAY-WRITE SIZE (LEN DATA)
                                                          INDEX VAL DATA)))

           :in-theory (e/d ((:induction bv-array-clear-range)
                            bv-array-clear-of-bv-array-clear-range
;bv-array-write UPDATE-NTH2
                            )
                           (BV-ARRAY-CLEAR-RANGE-OF-BV-ARRAY-CLEAR
;;                             bv-array-clear-range-same
;;                             BV-ARRAY-CLEAR-RANGE-OF-BV-ARRAY-CLEAR-ADJACENT2
;; ;                           BV-ARRAY-CLEAR-OF-BV-ARRAY-CLEAR-RANGE
;;                             BV-ARRAY-CLEAR-OF-BV-ARRAY-CLEAR-RANGE-ADJACENT1
;;                             BV-ARRAY-CLEAR-RANGE-OF-BV-ARRAY-CLEAR-ADJACENT1
;;                             UPDATE-NTH-BECOMES-UPDATE-NTH2-EXTEND-GEN
                            )))))

(defthm bv-array-clear-range-of-bv-array-write-too-high
  (implies (and (< high index)
                (< index len)
                (< high len)
                (<= alow high) ;"alow" comes alphabetically first
                (equal len (len data))
                (natp len)
                (natp alow)
                (natp high)
                (natp size)
                (natp index))
           (equal (bv-array-clear-range size len alow high (bv-array-write size len index val data))
                  (bv-array-write size len index val (bv-array-clear-range size len alow high data))))
  :hints (("Goal" :in-theory (e/d (BV-ARRAY-CLEAR-RANGE)
                                  (BV-ARRAY-CLEAR-OF-BV-ARRAY-CLEAR-RANGE ;looped
                                   ;; BV-ARRAY-CLEAR-OF-BV-ARRAY-CLEAR-DIFF
                                   )))))

(DEFTHM BV-ARRAY-CLEAR-RANGE-OF-BV-ARRAY-write-of-0-ADJACENT1
  (IMPLIES (AND (EQUAL LOWINDEX (+ 1 INDEX1))
                (< INDEX1 LEN)
                (< LOWINDEX LEN)
                (< HIGHINDEX LEN)
                (<= LOWINDEX HIGHINDEX)
                (NATP ELEM-SIZE)
                (NATP LEN)
                (NATP INDEX1)
                (NATP LOWINDEX)
                (NATP HIGHINDEX))
           (EQUAL (BV-ARRAY-CLEAR-RANGE ELEM-SIZE LEN LOWINDEX HIGHINDEX (BV-ARRAY-write ELEM-SIZE LEN INDEX1 0 LST))
                  (BV-ARRAY-CLEAR-RANGE ELEM-SIZE LEN INDEX1 HIGHINDEX LST)))
  :hints (("Goal" :in-theory (enable bv-array-write-of-0-becomes-bv-array-clear))))

(DEFTHM BV-ARRAY-CLEAR-RANGE-OF-BV-ARRAY-write-of-0-ADJACENT2
  (IMPLIES (AND (EQUAL INDEX1 (+ 1 HIGHINDEX))
                (< INDEX1 LEN)
                (< LOWINDEX LEN)
                (< HIGHINDEX LEN)
                (<= LOWINDEX HIGHINDEX)
                (NATP ELEM-SIZE)
                (NATP LEN)
                (NATP INDEX1)
                (NATP LOWINDEX)
                (NATP HIGHINDEX))
           (EQUAL (BV-ARRAY-CLEAR-RANGE ELEM-SIZE LEN LOWINDEX HIGHINDEX (BV-ARRAY-write ELEM-SIZE LEN INDEX1 0 LST))
                  (BV-ARRAY-CLEAR-RANGE ELEM-SIZE LEN LOWINDEX INDEX1 LST)))
  :hints (("Goal" :in-theory (enable bv-array-write-of-0-becomes-bv-array-clear))))

(DEFTHM BV-ARRAY-CLEAR-RANGE-OF-BV-ARRAY-WRITE-TOO-low
  (IMPLIES (AND (< INDEX alow)
                (< INDEX LEN)
                (< HIGH LEN)
                (<= ALOW HIGH)
                (EQUAL LEN (LEN DATA))
                (NATP LEN)
                (NATP ALOW)
                (NATP HIGH)
                (NATP SIZE)
                (NATP INDEX))
           (EQUAL (BV-ARRAY-CLEAR-RANGE SIZE LEN ALOW HIGH (BV-ARRAY-WRITE SIZE LEN INDEX VAL DATA))
                  (BV-ARRAY-WRITE SIZE LEN INDEX VAL (BV-ARRAY-CLEAR-RANGE SIZE LEN ALOW HIGH DATA))))
  :HINTS
  (("Goal"
    :IN-THEORY (E/D (BV-ARRAY-CLEAR-RANGE)
                    (BV-ARRAY-CLEAR-OF-BV-ARRAY-CLEAR-RANGE)))))

(defthm bv-array-clear-range-of-bv-array-write-both
  (implies (and (< high len)
                (equal len (len data))
                (natp len)
                (natp low)
                (natp high)
                (natp size)
                (<= low high)
                (< index (len data))
                (natp index))
           (equal (bv-array-clear-range size len low high (bv-array-write size len index val data))
                  (if (and (<= low index)
                           (<= index high))
                      (bv-array-clear-range size len low high data)
                    (bv-array-write size len index val (bv-array-clear-range size len low high data)))))
  :hints (("Goal" :in-theory (disable))))

(defthm bv-array-clear-of-bv-array-clear-range-contained
  (implies (and (<= lowindex index1)
                (<= index1 highindex)
                (< highindex len)
                (<= lowindex highindex)
                (natp elem-size)
                (natp len)
                (natp index1)
                (natp lowindex)
                (natp highindex))
           (equal (bv-array-clear elem-size len index1 (bv-array-clear-range elem-size len lowindex highindex lst))
                  (bv-array-clear-range elem-size len lowindex highindex lst)))
  :hints (("Goal" :expand ((BV-ARRAY-CLEAR-RANGE ELEM-SIZE LEN INDEX1 HIGHINDEX LST))
           :in-theory (enable bv-array-clear-range))))

(defthm take-of-bv-array-clear-range-irrel
  (implies (and (<= n lowindex)
                (natp len)
                (< highindex len)
;(<= lowindex highindex)
                (natp n)
                (< n len)
                (natp lowindex)
                (natp highindex))
           (equal (take n (bv-array-clear-range elem-size len lowindex highindex lst))
                  (bvchop-list elem-size (take n lst))))
  :hints (("Goal" :in-theory (e/d (bv-array-clear-range
                                   bv-array-clear bv-array-write update-nth2 ceiling-of-lg
                                                  ;;natp
                                                  take
                                                  UNSIGNED-BYTE-P-OF-INTEGER-LENGTH-GEN)
                                  (EQUAL-OF-UPDATE-NTH-new
                                   FIRSTN-BECOMES-TAKE-GEN
                                   natp)))))

(defthm bv-array-clear-range-of-bv-array-clear-range-adjacent1
  (implies (and (equal lowindex2 (+ 1 highindex1))
                (< lowindex1 len)
                (< highindex1 len)
;                (< lowindex2 len)
                (< highindex2 len)
                (<= lowindex1 highindex1)
                (<= lowindex2 highindex2) ;added back
                (natp elem-size)
                (natp len)
                (natp lowindex1)
                (natp highindex1)
                (natp lowindex2)
                (natp highindex2))
           (equal (bv-array-clear-range elem-size len lowindex1 highindex1 (bv-array-clear-range elem-size len lowindex2 highindex2 lst))
                  (bv-array-clear-range elem-size len lowindex1 highindex2 lst)))
  :hints (("Goal" :in-theory (enable bv-array-clear-range))))

(defthm bv-array-clear-range-of-bv-array-clear-range-adjacent2
  (implies (and (equal lowindex2 (+ 1 highindex1))
                (< lowindex1 len)
                (< highindex1 len)
                (< lowindex2 len)
                (< highindex2 len)
                (<= lowindex1 highindex1) ;added back
                (<= lowindex2 highindex2)
                (natp elem-size)
                (natp len)
                (natp lowindex1)
                (natp highindex1)
                (natp lowindex2)
                (natp highindex2))
           (equal (bv-array-clear-range elem-size len lowindex2 highindex2 (bv-array-clear-range elem-size len lowindex1 highindex1 lst))
                  (if (<= lowindex1 highindex1)
                      (bv-array-clear-range elem-size len lowindex1 highindex2 lst)
                    (bv-array-clear-range elem-size len lowindex2 highindex2 lst))))
  :hints (("Goal" :in-theory (enable bv-array-clear-range))))

(defthm nthcdr-of-bv-array-clear-range
  (implies (and (<= n lowindex)
                (<= n len)
                (< lowindex len) ;Mon Jul 19 20:46:59 2010
                (< highindex len) ;Mon Jul 19 20:46:59 2010
                (integerp len)
                (equal len (+ 1 highindex)) ; Mon Jul 19 20:49:41 2010 could drop?
                (natp n)
                (natp lowindex)
                (natp highindex))
           (equal (nthcdr n (bv-array-clear-range element-size len lowindex highindex lst))
                  (bv-array-clear-range element-size (- len n) (- lowindex n) (- highindex n) (nthcdr n lst))))
  :hints (("Goal" ; :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (bv-array-clear-range nthcdr) ()))))

(defthm nthcdr-of-bv-array-clear-range2
  (implies (and (< highindex n)
                (<= n len)
                (<= lowindex highindex)
                (integerp len)
                (natp n)
                (natp lowindex)
                (natp highindex))
           (equal (nthcdr n (bv-array-clear-range element-size len lowindex highindex lst))
                  (nthcdr n (bvchop-list element-size (take len lst)))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (bv-array-clear-range nthcdr) (
                                                          ;NTHCDR-OF-TAKE-BECOMES-SUBRANGE
                                                          )))))

(defthm car-of-BV-ARRAY-CLEAR-RANGE-of-0
  (implies (and (posp len)
                (natp highindex))
           (equal (CAR (BV-ARRAY-CLEAR-RANGE ELEM-SIZE LEN 0 HIGHINDEX LST))
                  0))
  :hints (("Goal" :expand (BV-ARRAY-CLEAR-RANGE ELEM-SIZE LEN 0 HIGHINDEX LST))))

(defthm cdr-of-bv-array-clear-range-2
  (implies (and (<= 1 lowindex)
                (<= 1 len)
                (< lowindex len)
                (< highindex len)
                (integerp len)
                (natp lowindex)
                (natp highindex))
           (equal (cdr (bv-array-clear-range element-size len lowindex highindex lst))
                  (bv-array-clear-range element-size (- len 1) (- lowindex 1) (- highindex 1) (cdr lst))))
  :hints (("Goal" :induct t
           :in-theory (enable bv-array-clear-range))))

(defthm take-of-bv-array-clear-range
  (implies (and ; (natp elem-size)
             (natp n)
             (natp len)
             (natp highindex)
             (< highindex len)
             (<= n (+ 1 highindex)))
           (equal (take n (bv-array-clear-range elem-size len 0 highindex lst))
                  (repeat n 0)))
  :hints (("Goal" :induct t
           :do-not '(generalize eliminate-destructors)
           :in-theory (enable take bv-array-clear-range take-when-most-known equal-of-append))))

(DEFTHM ALL-UNSIGNED-BYTE-P-OF-BV-ARRAY-CLEAR-range
  (IMPLIES (AND (<= ELEMENT-SIZE SIZE)
                (NATP SIZE)
                (NATP ELEMENT-SIZE))
           (ALL-UNSIGNED-BYTE-P SIZE (BV-ARRAY-CLEAR-range ELEMENT-SIZE LEN lowindex highindex LST)))
  :HINTS (("Goal" :IN-THEORY (ENABLE BV-ARRAY-CLEAR-range))))

;move
(local
  (defthm bvchop-list-of-repeat
    (equal (bvchop-list size (repeat n x))
           (repeat n (bvchop size x)))
    :hints (("Goal" :in-theory (enable bvchop-list repeat)))))

(defthmd bv-array-clear-range-redef-special
  (implies (and (equal len (len data)) ; this case
                (< highindex len)
                (<= lowindex highindex)
                (natp highindex)
                (natp lowindex))
           (equal (bv-array-clear-range element-size len lowindex highindex data)
                  (append (bvchop-list element-size (take lowindex data))
                          (repeat (+ 1 (- highindex lowindex)) 0)
                          (bvchop-list element-size (nthcdr (+ 1 highindex) data)))))
  :hints (("Goal" :in-theory (enable bv-array-clear-range bv-array-clear-redef equal-of-append))))

(defthmd bv-array-clear-range-redef
  (implies (and (< highindex len)
                (<= lowindex highindex)
                (natp len)
                (natp highindex)
                (natp lowindex))
           (equal (bv-array-clear-range element-size len lowindex highindex data)
                  (append (bvchop-list element-size (take lowindex data))
                          (repeat (+ 1 (- highindex lowindex)) 0)
                          (bvchop-list element-size (take (+ -1 (- highindex) len) (nthcdr (+ 1 highindex) data))))))
  :hints (("Goal" :in-theory (enable bv-array-clear-range bv-array-clear-redef equal-of-append))))
