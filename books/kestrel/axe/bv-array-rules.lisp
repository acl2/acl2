; bv-array rules
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2024 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; todo: move these out of axe

(include-book "kestrel/bv-lists/bv-array-clear" :dir :system)
(include-book "rules1")

;; (local (include-book "kestrel/arithmetic-light/mod-and-expt" :dir :system))
;; ;(local (include-book "arithmetic/equalities" :dir :system))
;; (local (include-book "kestrel/library-wrappers/arithmetic-inequalities" :dir :system))
(local (include-book "kestrel/lists-light/cons" :dir :system))
(local (include-book "kestrel/lists-light/repeat" :dir :system))
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
(local (include-book "kestrel/lists-light/update-nth" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
;; (local (include-book "kestrel/lists-light/nth" :dir :system))
;; (local (include-book "kestrel/lists-light/cdr" :dir :system))
(local (include-book "kestrel/lists-light/subrange" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))
;; (local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))
;; (local (include-book "kestrel/arithmetic-light/floor-and-expt" :dir :system))
;; (local (include-book "kestrel/bv/floor-mod-expt" :dir :system))
;; (local (include-book "kestrel/bv/trim-rules" :dir :system))
(local (include-book "kestrel/bv-lists/all-unsigned-byte-p2" :dir :system))
(local (include-book "kestrel/arithmetic-light/integer-length2" :dir :system))
;(local (include-book "kestrel/arithmetic-light/expt2" :dir :system))
;(local (include-book "kestrel/arithmetic-light/times" :dir :system))
;(local (include-book "kestrel/arithmetic-light/plus-and-times" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
;(local (include-book "kestrel/arithmetic-light/minus" :dir :system))
;(local (include-book "kestrel/arithmetic-light/mod2" :dir :system))
;(local (include-book "kestrel/arithmetic-light/rem" :dir :system))
;; (local (include-book "kestrel/arithmetic-light/truncate" :dir :system))
;; (local (include-book "kestrel/arithmetic-light/ceiling" :dir :system))
;; (local (include-book "kestrel/arithmetic-light/integer-length" :dir :system))
;; (local (include-book "kestrel/library-wrappers/ihs-quotient-remainder-lemmas" :dir :system)) ;drop
;; (local (include-book "kestrel/library-wrappers/ihs-logops-lemmas" :dir :system)) ;drop

;gross to mix theories?
(defthm bv-array-clear-of-cons
  (implies (and (< i len)
                (equal (+ -1 len) (len x))
                (natp i)
                (true-listp x) ;move to conclusion
                (natp len)
                (natp size)
                )
           (equal (bv-array-clear size len i (cons a x))
                  (if (zp i)
                      (cons 0 (bvchop-list size x))
                    (cons (bvchop size a) (bv-array-clear size (+ -1 len) (+ -1 i) x)))))
  :hints (("Goal" :in-theory (e/d (bv-array-clear bv-array-write update-nth2 ceiling-of-lg)
                                  (;UNSIGNED-BYTE-P-OF-+-OF-MINUS-ALT
                                   ;UNSIGNED-BYTE-P-OF-+-OF-MINUS
                                   ;;update-nth-becomes-update-nth2-extend-gen
                                   )))))

;;todo clear-nth becomes bv-array-clear?

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

(defthm bv-array-clear-of-0-arg2
  (equal (bv-array-clear size 0 index data)
         nil)
  :hints (("Goal" :in-theory (enable bv-array-clear))))

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

(defthm bv-array-clear-of-bv-array-clear-range
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
;bv-array-write UPDATE-NTH2
                            )
                           (BV-ARRAY-CLEAR-RANGE-OF-BV-ARRAY-CLEAR
                            bv-array-clear-range-same
                            BV-ARRAY-CLEAR-RANGE-OF-BV-ARRAY-CLEAR-ADJACENT2
;                           BV-ARRAY-CLEAR-OF-BV-ARRAY-CLEAR-RANGE
                            BV-ARRAY-CLEAR-OF-BV-ARRAY-CLEAR-RANGE-ADJACENT1
                            BV-ARRAY-CLEAR-RANGE-OF-BV-ARRAY-CLEAR-ADJACENT1
                            UPDATE-NTH-BECOMES-UPDATE-NTH2-EXTEND-GEN)))))

(defthm bv-array-clear-of-0-and-cons
  (implies (syntaxp (not (quotep a)))
           (equal (bv-array-clear size len 0 (cons a b))
                  (bv-array-clear size len 0 (cons 0 b))))
  :hints (("Goal" :in-theory (e/d (bv-array-clear bv-array-write update-nth2) (update-nth-becomes-update-nth2-extend-gen)))))

(defthm bv-array-clear-range-of-cons
  (implies (and (syntaxp (not (quotep a))) ;ffixme we really want to do it for anything but 0? add support for equal to make-axe-rules
                (< high len)
                (natp len)
                (natp high))
           (equal (bv-array-clear-range size len 0 high (cons a b))
                  (bv-array-clear-range size len 0 high (cons '0 b))))
  :hints (("Goal"
           :expand ((bv-array-clear-range size len 0 high (cons a b)))
           :in-theory (enable bv-array-clear-range subrange-of-cons))))

(defthm bv-array-clear-range-of-cons-of-cons
  (implies (and (syntaxp (not (and (quotep a)
                                   (quotep b)))) ;ffixme we really want to do it for anything but 0? add support for equal to make-axe-rules
                (< high len)
                (natp len)
                (posp high) ;gen?
                )
           (equal (bv-array-clear-range width len 0 high (cons a (cons b c)))
                  (bv-array-clear-range width len 0 high (append '(0 0) c))))
  :hints (("Goal" :in-theory (enable subrange-of-cons))))

(defthm bv-array-clear-range-of-append-of-cons
  (implies (and (syntaxp (not (quotep b))) ;ffixme we really want to do it for anything but 0? add support for equal to make-axe-rules
                (syntaxp (quotep a))
                (<= (len a) high)
                (< high len)
                (natp high)
                (natp len))
           (equal (bv-array-clear-range width len 0 high (append a (cons b c)))
                  (bv-array-clear-range width len 0 high (append (append a '(0)) c))))
  :hints (("Goal" :in-theory (enable ;list::nth-of-cons
                              natp subrange-of-cons))))

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

(defthmd array-write-of-0
  (equal (bv-array-write elem-size len index1 0 lst)
         (bv-array-clear elem-size len index1 lst))
  :hints (("Goal" :in-theory (enable bv-array-clear))))

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
           (EQUAL
            (BV-ARRAY-CLEAR-RANGE ELEM-SIZE LEN LOWINDEX HIGHINDEX (BV-ARRAY-write ELEM-SIZE LEN INDEX1 0 LST))
            (BV-ARRAY-CLEAR-RANGE ELEM-SIZE LEN INDEX1 HIGHINDEX LST)))
  :hints (("Goal" :in-theory (enable ARRAY-WRITE-of-0))))

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
           (EQUAL
            (BV-ARRAY-CLEAR-RANGE ELEM-SIZE LEN LOWINDEX HIGHINDEX (BV-ARRAY-write ELEM-SIZE LEN INDEX1 0 LST))
            (BV-ARRAY-CLEAR-RANGE ELEM-SIZE LEN LOWINDEX INDEX1 LST)))
  :hints (("Goal" :in-theory (enable ARRAY-WRITE-of-0))))

;gen!
(defthm bv-array-clear-range-of-append-one-more
  (implies (and (syntaxp (quotep z))
                (equal z (repeat (len z) 0))
                (< index (+ -1 (len z))) ;to prevent loops
                (< (len z) len)
                (natp index)
                (natp len)
                )
           (equal (bv-array-clear-range 32 len 0 index (binary-append z x))
                  (bv-array-clear-range 32 len 0 (+ -1 (len z)) (binary-append z x))))
  :hints (("Goal" :in-theory (e/d (equal-of-append nthcdr-of-cdr-combine-strong) (;EQUAL-OF-REPEAT-OF-LEN-SAME
                                                     )))))

(defthm bv-array-clear-length-1-of-list-zero
  (equal (bv-array-clear width 1 index '(0))
         '(0))
  :hints (("Goal" :in-theory (e/d (bv-array-clear bv-array-write update-nth2) (update-nth-becomes-update-nth2-extend-gen)))))

(defthm car-of-bv-array-clear
  (equal (car (bv-array-clear width len index data))
         (if (posp len)
             (if (zp (bvchop (ceiling-of-lg (nfix len)) index))
                 0
               (bvchop width (car data)))
           nil))
  :hints (("Goal" :in-theory (e/d (bv-array-clear bv-array-write update-nth2) (update-nth-becomes-update-nth2-extend-gen)))))

(defthm car-of-bv-array-clear-range
  (implies (and (natp high)
                (natp low)
                (<= low high) ;Mon Jul 19 21:20:04 2010
                (< high len) ;Mon Jul 19 21:20:04 2010
                (posp len))
           (equal (car (bv-array-clear-range width len low high data))
                  (if (zp low)
                      0
                    (bvchop width (car data)))))
  :hints (("Goal"
           :in-theory (e/d (bv-array-clear-range
                            subrange-of-cons)
                                  ( ;list::equal-append-reduction!
                                   cons-onto-repeat
                                   )))))

(defthm cdr-of-bv-array-clear
  (implies (and (posp len)
                (< index len) ;Mon Jul 19 21:20:04 2010
                (natp index))
           (equal (cdr (bv-array-clear width len index data))
                  (if (zp index)
                      (bvchop-list width (SUBRANGE 1 (+ -1 LEN) DATA))
                    (bv-array-clear width (+ -1 len) (+ -1 index) (cdr data)))))
  :hints (("Goal"
           :cases ((< len 2))
           :in-theory (e/d (bv-array-clear bv-array-write-opener update-nth2 subrange)
                                  (GETBIT-OF-BV-ARRAY-READ-HELPER ;yuck
                                   ;LIST::UPDATE-NTH-EQUAL-REWRITE-ALT
                                   update-nth-becomes-update-nth2-extend-gen)))))

(defthm bv-array-clear-range-of-1-and-cons-of-0
  (implies (and (<= 1 high)
                (< high len)
                (posp len)
                (equal len (+ 1 (len data)))
                (natp high)
                (natp width))
           (equal (bv-array-clear-range width len 1 high (cons '0 data))
                  (bv-array-clear-range width len 0 high (cons '0 data))))
  :hints (("Goal" ;:expand ((bv-array-clear-range width len 1 high (cons 0 data)))
           :in-theory (e/d (bv-array-clear-range subrange-of-cons subrange cdr-take-plus-1)
                           ( ;list::equal-append-reduction!
                            cons-onto-repeat
                            nthcdr-of-take-becomes-subrange
                            cdr-of-take-becomes-subrange-better
                            take-of-nthcdr-becomes-subrange
                            take-of-cdr-becomes-subrange ;looped and no theory invar
                            )))))

(defthm cdr-of-bv-array-clear-range
  (implies (and (natp high)
                (natp width)
                (<= low high) ;Mon Jul 19 21:20:04 2010
                (< high len) ;Mon Jul 19 21:20:04 2010
                (equal len (len data)) ;Mon Jul 19 21:40:02 2010
                (natp low) ;gen?
                (posp len))
           (equal (cdr (bv-array-clear-range width len low high data))
                  (if (zp low)
                      (bv-array-clear-range width (+ -1 len) 0 (+ -1 high) (cdr data))
                    (bv-array-clear-range width (+ -1 len) (+ -1 low) (+ -1 high) (cdr data)))))
  :hints (("subgoal *1/2" :cases ((< HIGH (BINARY-+ '2 LOW))))
          ("Goal" :do-not '(generalize eliminate-destructors)
           :induct (BV-ARRAY-CLEAR-RANGE WIDTH LEN LOW HIGH DATA)
           :in-theory (e/d (bv-array-clear-range subrange-of-cons consp-of-cdr equal-of-append)
                                  ( ;list::equal-append-reduction!
                                   cons-onto-repeat
                                   ;LIST::LEN-POS-REWRITE
                                   )))))

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

(defthm bv-array-clear-of-bv-array-write-both
  (implies (and (natp esize)
                (natp key1)
                (< key1 len)
                (natp key2)
                (< key2 len)
                (natp len)
                (equal len (len lst)))
           (equal (bv-array-clear esize len key1 (bv-array-write esize len key2 val lst))
                  (if (equal key1 key2)
                      (bv-array-clear esize len key1 lst)
                    (bv-array-write esize len key2 val (bv-array-clear esize len key1 lst))))))

;gross
 ;might be expensive
(defthmd cons-becomes-bv-array-write-size-8
  (implies (unsigned-byte-p 8 a)
           (equal (cons a nil)
                  (bv-array-write 8 1 0 a (list 0))))
  :hints (("Goal" :in-theory (e/d (update-nth2 bv-array-write) (;update-nth-becomes-update-nth2-extend-gen
                                                                )))))

;gen and use this more
;yikes! this lets data be a quotep
(defthmd cons-becomes-bv-array-write-size-8-gen
  (implies (and (unsigned-byte-p 8 a)
                (TRUE-LISTP data)
                (all-unsigned-byte-p 8 data))
           (equal (cons a data)
                  (bv-array-write 8 (+ 1 (len data)) 0 a (cons 0 data ))))
  :hints
  (("Goal" :in-theory (e/d (update-nth2 bv-array-write) (;update-nth-becomes-update-nth2-extend-gen
                                                         )))))

;; ;move
;; (defthmd bvchop-of-nth2-becomes-bv-array-read
;;   (implies (and (unsigned-byte-p n x)
;;                 (natp n)
;;                 (natp size))
;;            (equal (bvchop size (nth2 n x data))
;;                   (bv-array-read size (expt 2 n) x data)))
;;   :hints (("Goal" :in-theory (e/d (bv-array-read bvchop-when-i-is-not-an-integer nth2 ceiling-of-lg)
;;                                   (nth-of-bv-array-write-becomes-bv-array-read)))))

;rename
(defthmd nth-becomes-bv-array-read2
  (implies (and (all-unsigned-byte-p free data)
                (natp n)
                (< n (len data)))
           (equal (nth n data)
                  (bv-array-read free (len data) n data)))
  :hints (("Goal" :in-theory (e/d (bv-array-read ceiling-of-lg)
                                  (NTH-OF-BV-ARRAY-WRITE-BECOMES-BV-ARRAY-READ)))))

(theory-invariant (incompatible (:definition bv-array-read) (:rewrite NTH-BECOMES-BV-ARRAY-READ2)))

(defthm bvchop-of-nth-becomes-bv-array-read
  (implies (and (all-unsigned-byte-p size data) ;not logically necessary but helps prevent this rule from firing on heterogeneous lists.  this might be bad if the bvchop size is smaller than the array elems... fffixme - had size here -- now trying with free
                (natp n))
           (equal (bvchop size (nth n data))
                  (if (< n (len data))
                      (bv-array-read size (len data) n data)
                    0)))
  :hints (("Goal" :in-theory (e/d (bv-array-read-opener ;list::nth-with-large-index
                                   )
                                  (nth-of-bv-array-write-becomes-bv-array-read
                                   NTH-BECOMES-BV-ARRAY-READ2)))))

(defthmd bvchop-of-nth-becomes-bv-array-read2
  (implies (and ;(all-unsigned-byte-p size data) ;not logically necessary but helps prevent this rule from firing on heterogeneous lists.  this might be bad if the bvchop size is smaller than the array elems... fffixme - had size here -- now trying with free
                (natp n))
           (equal (bvchop size (nth n data))
                  (if (< n (len data))
                      (bv-array-read size (len data) n data)
                    0)))
  :hints (("Goal" :in-theory (e/d (bv-array-read-opener ;LIST::NTH-WITH-LARGE-INDEX
                                   )
                                  (NTH-OF-BV-ARRAY-WRITE-BECOMES-BV-ARRAY-READ
                                   NTH-BECOMES-BV-ARRAY-READ2)))))

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
  :hints (("Goal" :in-theory (disable BV-ARRAY-WRITE-EQUAL-REWRITE-ALT BV-ARRAY-WRITE-EQUAL-REWRITE))))
