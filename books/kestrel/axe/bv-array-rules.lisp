; bv-array rules
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

;; todo: move these out of axe

(include-book "kestrel/bv-lists/bv-array-clear" :dir :system)
(include-book "kestrel/bv-lists/bv-array-clear-range" :dir :system)
(include-book "rules1") ; todo
(include-book "kestrel/lists-light/prefixp-def" :dir :system)
(local (include-book "kestrel/lists-light/prefixp" :dir :system))
(local (include-book "kestrel/lists-light/prefixp2" :dir :system))

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
;; (local (include-book "kestrel/bv/floor-mod-expt" :dir :system))
;; (local (include-book "kestrel/bv/trim-rules" :dir :system))
(local (include-book "kestrel/bv-lists/all-unsigned-byte-p2" :dir :system))
(local (include-book "kestrel/arithmetic-light/integer-length2" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))

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

;gen!
(defthm bv-array-clear-range-of-append-one-more
  (implies (and (syntaxp (quotep z))
                (equal z (repeat (len z) 0))
                (< index (+ -1 (len z))) ;to prevent loops
                (< (len z) len)
                (natp index)
                (natp len))
           (equal (bv-array-clear-range 32 len 0 index (binary-append z x))
                  (bv-array-clear-range 32 len 0 (+ -1 (len z)) (binary-append z x))))
  :hints (("Goal" :in-theory (e/d (equal-of-append nthcdr-of-cdr-combine-strong) (;EQUAL-OF-REPEAT-OF-LEN-SAME
                                                     )))))

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

(defthmd cons-becomes-bv-array-write-size-1
  (implies (unsigned-byte-p 1 a)
           (equal (cons a nil)
                  (bv-array-write 1 1 0 a (list 0))))
  :hints (("Goal" :in-theory (enable update-nth2 bv-array-write))))

(defthmd cons-becomes-bv-array-write-size-4
  (implies (unsigned-byte-p 4 a)
           (equal (cons a nil)
                  (bv-array-write 4 1 0 a (list 0))))
  :hints (("Goal" :in-theory (enable update-nth2 bv-array-write))))

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

;disable?
(defthmd bvchop-of-nth-becomes-bv-array-read
  (implies (and (all-unsigned-byte-p size data) ;not logically necessary but helps prevent this rule from firing on heterogeneous lists.  this might be bad if the bvchop size is smaller than the array elems... fffixme - had size here -- now trying with free
                (natp n))
           (equal (bvchop size (nth n data))
                  (if (< n (len data))
                      (bv-array-read size (len data) n data)
                    0)))
  :hints (("Goal" :in-theory (e/d (bv-array-read-opener ;list::nth-with-large-index
                                   )
                                  (nth-of-bv-array-write-becomes-bv-array-read)))))

(theory-invariant (incompatible (:definition bv-array-read) (:rewrite bvchop-of-nth-becomes-bv-array-read)))

(defthmd bvchop-of-nth-becomes-bv-array-read2
  (implies (and ;(all-unsigned-byte-p size data) ;not logically necessary but helps prevent this rule from firing on heterogeneous lists.  this might be bad if the bvchop size is smaller than the array elems... fffixme - had size here -- now trying with free
                (natp n))
           (equal (bvchop size (nth n data))
                  (if (< n (len data))
                      (bv-array-read size (len data) n data)
                    0)))
  :hints (("Goal" :in-theory (e/d (bv-array-read-opener ;LIST::NTH-WITH-LARGE-INDEX
                                   )
                                  (NTH-OF-BV-ARRAY-WRITE-BECOMES-BV-ARRAY-READ)))))

(theory-invariant (incompatible (:definition bv-array-read) (:rewrite bvchop-of-nth-becomes-bv-array-read2)))

(defthm equal-of-bv-array-write-same
  (implies (and (natp width)
                (natp index)
                (< index len)
                (integerp len))
           (equal (equal x (bv-array-write width len index val x))
                  (and (equal len (len x))
                       (true-listp x)
                       (all-unsigned-byte-p width x)
                       (equal (bvchop width val)
                              (bv-array-read width len index x)))))
  :hints (("Goal" :cases ((equal len (len x))))))

(defthm equal-of-bv-array-write-and-bv-array-write-same
  (implies (and (natp width)
                (natp index)
                (natp index2)
                (< index len)
                (< index2 len)
                (integerp len)
                (true-listp data)
                (all-unsigned-byte-p width data)
                (equal len (len data)))
           (equal (equal (bv-array-write width len index2 val2 data)
                         (bv-array-write width len index val data))
                  (if (equal index index2)
                      (equal (bvchop width val)
                             (bvchop width val2))
                    (and (equal (bvchop width val2)
                                (bv-array-read width len index2 data))
                         (equal (bvchop width val)
                                (bv-array-read width len index data))))))
  :hints (("Goal" :in-theory (e/d (bv-array-read-of-bv-array-write-both) (BV-ARRAY-READ-OF-BV-ARRAY-WRITE)))))

(defthm prefixp-of-bv-array-write-when-prefixp
  (implies (and (< (len x) len)
                (all-unsigned-byte-p 8 data)
                (prefixp x data)
                (natp len))
           (equal (prefixp x (bv-array-write '8 len (len x) val data))
                  t))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :use (:instance ALL-UNSIGNED-BYTE-P-OF-TRUE-LIST-FIX
                           (size 8)
                           (lst x))
           :in-theory (e/d (bv-array-write ceiling-of-lg UPDATE-NTH2 PREFIXP-REWRITE-gen
                                           equal-of-true-list-fix-and-true-list-fix-forward)
                           (ALL-UNSIGNED-BYTE-P-OF-TRUE-LIST-FIX
                            )))))

;rename
(defthm bvlt-of-len-and-len-when-prefixp
  (implies (and (prefixp x free)
                (equal y free)
                (unsigned-byte-p size (len x))
                (unsigned-byte-p size (len y)))
           (equal (bvlt size (len y) (len x))
                  nil))
  :hints (("Goal" :in-theory (enable bvlt prefixp))))
