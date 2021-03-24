; Rules about bv-array operations
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/arithmetic-light/power-of-2p" :dir :system)
(include-book "bv-arrayp")
(include-book "bv-array-read")
(include-book "bv-array-write")
(include-book "width-of-widest-int")
(include-book "bvxor-list")
(include-book "kestrel/bv/bvif" :dir :system)
(include-book "kestrel/bv/bitxor" :dir :system)
(include-book "kestrel/lists-light/all-equal-dollar" :dir :system)
(include-book "kestrel/lists-light/repeat" :dir :system)
(include-book "kestrel/utilities/myif" :dir :system)
(include-book "kestrel/utilities/forms" :dir :system)
(include-book "ihs/basic-definitions" :dir :system) ;for logext
(local (include-book "kestrel/lists-light/cons" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/lists-light/update-nth" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))
(local (include-book "kestrel/lists-light/cdr" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
(local (include-book "kestrel/lists-light/all-equal-dollar2" :dir :system)) ;for ALL-EQUAL$-WHEN-TRUE-LISTP
(local (include-book "kestrel/lists-light/memberp" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt2" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/arithmetic-light/integer-length2" :dir :system))
(local (include-book "kestrel/bv/unsigned-byte-p" :dir :system))
(local (include-book "kestrel/bv/logext" :dir :system))
(local (include-book "all-unsigned-byte-p2"))

;move
(defthm take-of-repeat-same
  (equal (take len (repeat len x))
         (repeat len x))
  :hints (("Goal" :in-theory (enable repeat take))))

(in-theory (disable len))

(defthm all-integerp-of-update-nth2
  (implies (and (all-integerp lst)
                (integerp val)
                (natp index)
                (equal len (len lst))
                (<= index (len lst)))
           (all-integerp (update-nth2 len index val lst)))
  :hints (("Goal"
           :induct t
;           :cases ((< (LEN LST) (BINARY-+ '1 INDEX)))
           :in-theory (e/d (UPDATE-NTH2 ;LIST::LEN-UPDATE-NTH-BETTER
                            len) (len-of-cdr
                                  )))))

;not true any more?
;; (defthm bv-array-write-when-index-not-positive-cheap
;;   (implies (< index 0)
;;            (equal (bv-array-write element-size len index val data)
;;                   (bv-array-write element-size len 0 val data)))
;;   :rule-classes ((:rewrite :backchain-limit-lst (0)))
;;   :hints (("Goal" :in-theory (e/d (bv-array-write update-nth2) ()))))

;for axe?
(defthm integerp-of-bv-array-read
  (integerp (bv-array-read element-size len index data)))

;for axe?
(defthm natp-of-bv-array-read
  (natp (bv-array-read element-size len index data)))

(defthmd bv-array-read-of-bv-array-write-diff
  (implies (and (not (equal index1 index2))
                (natp index1)
                (natp index2)
                (< index1 len)
                (< index2 len)
                (integerp len))
           (equal (bv-array-read width len index1 (bv-array-write width len index2 val lst))
                  (bv-array-read width len index1 lst)))
  :hints (("Goal" :in-theory (enable bvchop-when-i-is-not-an-integer bv-array-read-opener update-nth2 ceiling-of-lg
                                     bv-array-write))))

(defthmd bv-array-read-of-bv-array-write-diff-safe
  (implies (and (syntaxp (and (quotep index1)
                              (quotep index2)))
                (not (equal index1 index2))
;                (equal len (len lst)) ;bozo?
                (natp index1)
                (natp index2)
                (< index1 len)
                (< index2 len)
                (integerp len))
           (equal (bv-array-read width len index1 (bv-array-write width len index2 val lst))
                  (bv-array-read width len index1 lst)))
  :hints (("Goal" :in-theory (enable bv-array-read-of-bv-array-write-diff))))

;letting the lens differ is new! fixme let the lens differ on other similar lemmas?
(defthm bv-array-read-of-bv-array-write-same
  (implies (and (natp index)
                (< index len2)
                (<= len2 len)
                (integerp len)
                (integerp len2))
           (equal (bv-array-read width len index (bv-array-write width len2 index val lst))
                  (bvchop width val)))
  :hints (("Goal" :in-theory (e/d (bv-array-read-opener bv-array-write ceiling-of-lg) ()))))

(defund bv-array-clear (element-size len index data)
  (declare (xargs :guard (and (natp len)
                              (natp index)
                              (ALL-INTEGERP data)
                              (<= len (len data))
                              (< index (len data))
                              (natp element-size)
                              (true-listp data))))
  (bv-array-write element-size len index 0 data))

(defthm true-listp-of-bv-array-clear
  (true-listp (bv-array-clear element-size len key lst))
  :hints (("Goal" :in-theory (enable bv-array-clear))))

;analogues of the bv-array-write theorems?

(defthm len-of-bv-array-clear
  (equal (len (bv-array-clear element-size len key lst))
         (nfix len))
  :hints (("Goal" :in-theory (e/d (bv-array-clear) ()))))

(defthm all-integerp-of-bv-array-clear
  (all-integerp (bv-array-clear element-size len key lst))
  :hints (("Goal" :in-theory (enable bv-array-clear))))

(defun bv-array-clear-range (esize len lowindex highindex data)
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

(defthm len-of-bv-array-clear-range
  (equal (len (bv-array-clear-range esize len lowindex highindex data))
         (nfix len)))

(defthm all-integerp-of-bv-array-clear-range
  (all-integerp (bv-array-clear-range esize len lowindex highindex data)))

(verify-guards bv-array-clear-range :hints (("Goal" :do-not-induct t)))

(defthm bv-array-read-of-bvchop-helper
  (implies (and (<= m n)
                (natp n)
                (natp m))
           (equal (BV-ARRAY-READ size (expt 2 m) (BVCHOP n INDEX) VALS)
                  (BV-ARRAY-READ size (expt 2 m) INDEX VALS)))
  :hints (("Goal" :in-theory (enable bv-array-read ceiling-of-lg))))

(defthm bv-array-read-of-bvchop
  (implies (and (equal len (expt 2 (+ -1 (integer-length len)))) ;len is a power of 2
                (<= (+ -1 (integer-length len)) n)
                (natp len)
                (natp n))
           (equal (bv-array-read size len (bvchop n index) vals)
                  (bv-array-read size len index vals)))
  :hints (("Goal" :in-theory (disable bv-array-read-of-bvchop-helper
                                      ;collect-constants-times-equal ;fixme
                                      )
           :use (:instance bv-array-read-of-bvchop-helper (m (+ -1 (integer-length len)))))))

;or do we want to go to nth?
(defthm bv-array-read-of-take
  (implies (posp len)
           (equal (bv-array-read elem-size len index (take len array))
                  (bv-array-read elem-size len index array)))
  :hints (("Goal" :cases ((posp len))
           :in-theory (enable bv-array-read))))

;kind of gross to mix theories like this?
(defthm bv-array-read-of-cons
  (implies (and (natp len)
                (< 0 index)
                (< index len)
                (natp index))
           (equal (BV-ARRAY-READ element-size len index (cons a b))
                  (BV-ARRAY-READ element-size (+ -1 len) (+ -1 index) b)))
  :hints (("Goal"
           :cases ((equal index (+ -1 len)))
           :in-theory (enable ;LIST::NTH-OF-CONS
                       bv-array-read unsigned-byte-p-of-integer-length-gen ceiling-of-lg))))

(defthm bv-array-read-of-cons-base
  (implies (and (natp len)
                (< 0 len) ;new!
                )
           (equal (BV-ARRAY-READ element-size len 0 (cons a b))
                  (bvchop element-size a)))
  :hints (("Goal" :in-theory (enable ;LIST::NTH-OF-CONS
                              BVCHOP-WHEN-I-IS-NOT-AN-INTEGER bv-array-read))))

(defthm bv-array-read-of-cons-both
  (implies (and (syntaxp (not (and (quotep a)  ;prevent application to a constant array
                                   (quotep b))))
                (natp len)
                ;(< 0 index)
                (< index len)
                (natp index))
           (equal (bv-array-read element-size len index (cons a b))
                  (if (equal 0 index)
                      (bvchop element-size a)
                  (bv-array-read element-size (+ -1 len) (+ -1 index) b)))))

(defthm bv-array-read-of-bv-array-write-tighten
  (implies (and (< esize1 esize2)
                (equal len (len data))
                (natp index2)
                (< index2 len)
                (< index len)
                (natp esize1)
                (natp esize2)
                (natp index))
           (equal (bv-array-read esize1 len index (bv-array-write esize2 len index2 val data))
                  (bv-array-read esize1 len index (bv-array-write esize1 len index2 val data))))
  :hints (("Goal" :in-theory (enable bv-array-read bv-array-write BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))))


(defthm bv-array-read-of-bvchop-list
  (implies (and (equal (len data) len)
                (< 0 len)
                (natp esize))
           (equal (bv-array-read esize len index (bvchop-list esize data))
                  (bv-array-read esize len index data)))
  :hints (("Goal" :in-theory (enable bv-array-read bvchop-when-i-is-not-an-integer))))

;bozo combine these?
;drop some hyps?
;allow widths to differ?
(defthm bv-array-read-of-bvchop-list2
  (implies (and (natp width)
                (integerp len)
                (< index len)
                (natp index)
                (< 0 len))
           (equal (bv-array-read width len index (bvchop-list width lst))
                  (bv-array-read width len index lst)))
  :hints (("Goal" :in-theory (e/d (;LIST::NTH-WITH-LARGE-INDEX
                                   NTH-WHEN-<=-LEN
                                   bv-array-read BVCHOP-WHEN-I-IS-NOT-AN-INTEGER)
                                  ()))))

(defthmd bv-array-read-when-data-isnt-an-all-unsigned-byte-p
  (implies (and (syntaxp (and (quotep data)
                              (quotep esize)))
                (not (all-unsigned-byte-p esize data))
                (equal (len data) len)
                (natp esize)
                (< 0 len))
           (equal (bv-array-read esize len index data)
                  (bv-array-read esize len index (bvchop-list esize data))))
  :hints
  (("Goal"
    :cases ((<= (len data) (bvchop isize index)))
    :in-theory (enable ;bvnth
                bvchop-when-i-is-not-an-integer
;list::nth-with-large-index
                ))))

;bozo more like this?  gen the 0?
(defthm bv-array-read-non-negative
  (equal (< (bv-array-read esize len index data) 0)
         nil))



;move?
(defthm bvchop-list-does-nothing-better
  (implies (and (all-unsigned-byte-p size lst)
;                (natp size)
                (true-listp lst))
           (equal (bvchop-list size lst) lst))
  :hints
  (("Goal"
    :in-theory (enable bvchop-list all-unsigned-byte-p))))

(defthm bvchop-list-does-nothing-better-2
  (implies (and (all-unsigned-byte-p size lst)
;                (natp size)
                )
           (equal (bvchop-list size lst)
                  (true-list-fix lst)))
  :hints
  (("Goal"
    :in-theory (enable bvchop-list all-unsigned-byte-p))))

(defthm bvchop-list-does-nothing-rewrite
  (equal (equal x (bvchop-list size x))
         (and (true-listp x)
              (all-unsigned-byte-p (nfix size) x)))
  :hints (("Goal" :in-theory (enable all-unsigned-byte-p bvchop-list))))

(defthmd bvchop-list-does-nothing-rewrite-alt
  (equal (equal (bvchop-list size x) x)
         (and (true-listp x)
              (all-unsigned-byte-p (nfix size) x)))
  :hints (("Goal" :use (:instance bvchop-list-does-nothing-rewrite)
           :in-theory (disable bvchop-list-does-nothing-rewrite
                               bvchop-list-does-nothing-better))))

(defthm all-unsigned-byte-p-of-update-nth
  (implies (and (unsigned-byte-p m val)
                (natp m)
;                (natp n)
                (all-unsigned-byte-p m lst))
           (equal (all-unsigned-byte-p m (update-nth n val lst))
                  (<= (nfix n) (len lst))))
  :hints (("Goal" :in-theory (enable update-nth all-unsigned-byte-p))))

(defthm all-unsigned-byte-p-of-update-nth2
  (implies (and (ALL-UNSIGNED-BYTE-P WIDTH lst)
                (unsigned-byte-p width val)
                (natp width)
                (natp index)
                (<= LEN (LEN (UPDATE-NTH INDEX VAL LST)))
                (< index (len lst)))
           (ALL-UNSIGNED-BYTE-P WIDTH (UPDATE-NTH2 LEN INDEX val lst)))
  :hints (("Goal" :in-theory (e/d (UPDATE-NTH2) (;NTHCDR-OF-TAKE-BECOMES-SUBRANGE
                                                 ;;TAKE-OF-NTHCDR-BECOMES-SUBRANGE
                                                 )))))

(defthm bv-array-read-shorten-data
  (implies (and (syntaxp (and (quotep data) ;new (was expensive without)
                              (quotep len))) ;new (was expensive without)
                (< len (len data))
                (all-integerp data)
                (posp len))
           (equal (bv-array-read element-size len index data)
                  (bv-array-read element-size len index (take len data))))
  :hints (("Goal" :in-theory (enable bv-array-read))))


;; (defthm bv-array-read-of-logext-list
;;   (implies (and (< index (len lst))
;;                 (<= size size2)
;;                 (equal len (len lst))
;;                 (natp index)
;;                 (natp len)
;;                 (natp size)
;;                 (integerp size2)
;;                 )
;;            (equal (BV-ARRAY-READ size len index (LOGEXT-LIST size2 lst))
;;                   (BV-ARRAY-READ size len index lst))
;;            )
;;   :hints (("Goal" :in-theory (enable BVCHOP-WHEN-I-IS-NOT-AN-INTEGER bv-array-read))))

(in-theory (disable bvchop-list))

;move
(defthm bvchop-list-of-update-nth
  (implies (and (natp n)
                (<= n (len lst))
                )
           (equal (bvchop-list m (update-nth n val lst))
                  (update-nth n (bvchop m val)  (bvchop-list m lst))))
  :hints (("Goal" :expand (UPDATE-NTH 1 VAL LST)
           :in-theory (e/d (bvchop-list update-nth) (;LIST::UPDATE-NTH-EQUAL-REWRITE
                                                     )))))

;; I'm going to try disabling this, now that we are not trimming array reads...
;hope the nfixes are okay - could make a function min-nfix..
(defthmd bvchop-of-bv-array-read
  (equal (bvchop n (bv-array-read element-size len index data))
         (bv-array-read (min (nfix n) (ifix element-size)) len index data))
  :hints (("Goal"
;           :cases ((natp n))
           :in-theory (e/d (bv-array-read natp)
                           (;list::nth-of-cons
                            )))))

(defthm bvchop-of-bv-array-read-same
  (equal (bvchop element-size (bv-array-read element-size len index data))
         (bv-array-read element-size len index data))
  :hints (("Goal"
;           :cases ((natp n))
           :in-theory (e/d (bv-array-read natp)
                           (;list::nth-of-cons
                            )))))


(defthm bv-array-read-of-0-arg1
  (equal (bv-array-read 0 len index data)
         0)
  :hints (("Goal" :in-theory (enable bv-array-read))))

(defthm BV-ARRAY-READ-when-width-negative
  (implies (< width 0)
           (equal (BV-ARRAY-READ width len INDEX data)
                  0))
  :hints (("Goal" :in-theory (enable BV-ARRAY-READ))))

(defthm bv-array-read-of-bv-array-write-both
  (implies (and (equal len (len lst))
                (natp index1)
                (natp index2)
                (< index1 len)
                (< index2 len)
                (integerp len))
           (equal (bv-array-read width len index1 (bv-array-write width len index2 val lst))
                  (if (not (equal index1 index2))
                      (bv-array-read width len index1 lst)
                    (bvchop width val))))
  :hints
  (("Goal" :in-theory (e/d (bvchop-when-i-is-not-an-integer
                            bv-array-read
                            ceiling-of-lg
                            bv-array-write) ()))))

;; (thm
;;  (implies (and (< x y)
;;                (natp x)
;;                (natp y))
;;           (unsigned-byte-p (INTEGER-LENGTH (+ -1 y)) x)))

;this may allow us to not open ceiling-of-lg so much
(defthm bvchop-of-ceiling-of-lg-when-<
  (implies (and (< x y) ;allow = (for powers of 2 we get 0?)
                (natp x)
                (natp y))
           (equal (bvchop (ceiling-of-lg y) x)
                  x))
  :hints (("Goal" :in-theory (enable ceiling-of-lg))))

;gross because it mixes theories?
;fixme could make an append operator with length params for two arrays..
;does this depend on weird behavior of bv-array-read that may change?
(defthm bv-array-read-of-append
  (implies (and; (equal len (+ (len x) (len y))) ;gen?
                (< index len)
                (natp len)
                (natp index))
           (equal (bv-array-read width len index (binary-append x y))
                  (if (< index (len x))
                      (bv-array-read width (len x) index x)
                    (bv-array-read width
                                   (- len (len x)) ;(len y)
                                   (- index (len x)) y))))
  :hints (("Goal"
           :cases ((equal 0 (len y)))
           :in-theory (enable bv-array-read ;-opener
                              natp))))

;use bv-array-read-of-append?
(defthm bv-array-read-of-append-of-cons
  (implies (and (equal (len x) index)
                (< index len)
                (natp len)
                (natp index))
           (equal (bv-array-read width len index (binary-append x (cons a b)))
                  (bvchop width a)))
  :hints (("Goal" :in-theory (enable bv-array-read ceiling-of-lg))))

(defund append-arrays (width len1 array1 len2 array2)
  (declare (xargs :guard (and (natp len1)
                              (natp len2)
                              (natp width)
                              (true-listp array1)
                              (true-listp array2))))
  (bvchop-list width (append (take len1 array1)
                              (take len2 array2))))

(defthm len-of-append-arrays
  (equal (len (append-arrays width len1 array1 len2 array2))
         (+ (nfix len1) (nfix len2)))
  :hints (("Goal" :in-theory (enable append-arrays))))

(defthm all-unsigned-byte-p-of-append-arrays
  (implies (natp size) ;move to cons?
           (all-unsigned-byte-p size (append-arrays size a b c d)))
  :hints (("Goal" :in-theory (enable append-arrays))))

;gross because it mixes theories?
;fixme could make an append operator with length params for two arrays..
(defthm bv-array-read-of-append-arrays
  (implies (and (equal len (+ len1 len2))
                (< index len)
                (natp len1)
                (natp len2)
                (natp index))
           (equal (bv-array-read width len index (append-arrays width len1 x len2 y))
                  (if (< index len1)
                      (bv-array-read width len1 index x)
                    (bv-array-read width len2 (- index len1) y))))
  :hints (("Goal" :in-theory (enable bv-array-read-opener append-arrays))))


;rename and gen
(defthm equal-of-bvchop-and-bv-array-read
  (implies (and (natp n)
                (< n 16)
                )
           (equal (equal (bvchop 8 (nth n data)) (bv-array-read 8 16 n data))
                  t))
  :hints (("Goal" :in-theory (e/d (bv-array-read bvchop-when-i-is-not-an-integer)
                                  ()))))

;rename and gen
(defthm equal-of-bvchop-and-bv-array-read-gen
  (implies (and (equal m n)
                (natp m)
                (< n 16)
                )
           (equal (equal (bvchop 8 (nth n data))
                         (bv-array-read 8 16 m data))
                  t))
  :hints (("Goal" :use (:instance equal-of-bvchop-and-bv-array-read))))

;move
(defthm bv-array-write-of-bvchop-arg3
  (implies (and (<= (ceiling-of-lg len) size)
                (integerp size))
           (equal (bv-array-write element-size len (bvchop size index) val data)
                  (bv-array-write element-size len index val data)))
  :hints (("Goal" :in-theory (enable bv-array-write))))

;move
(defthm bv-array-write-of-bvchop-arg4
  (implies (and (<= element-size size)
                (integerp size))
           (equal (bv-array-write element-size len index (bvchop size val) data)
                  (bv-array-write element-size len index val data)))
  :hints (("Goal" :in-theory (e/d (bv-array-write update-nth2) (;UPDATE-NTH-BECOMES-UPDATE-NTH2-EXTEND-GEN
                                                                 )))))

;maybe change bv-array-read to give 0 for an out-of-bounds index (after the index is chopped - not an issue for a power of 2?)
;there is also a version with work-hard around the first two hyps
(defthm bv-array-read-of-bv-array-write-both-better
  (implies (and (< index1 len) ;try to drop this - is the behavior right?
                (< index2 len) ;Mon Jul 19 20:50:58 2010
                (natp width2)
                (<= width width2) ;other case?
                (integerp len)
                (natp index1)
                (natp index2))
           (equal (bv-array-read width len index1 (bv-array-write width2 len index2 val lst))
                  (if (not (equal index1 index2))
                      (bv-array-read width len index1 lst)
                    (bvchop width val))))
  :hints
  (("Goal" :in-theory (e/d (bvchop-when-i-is-not-an-integer
                            ceiling-of-lg
                            bv-array-read
;list::nth-with-large-index-2
                            bv-array-write)
                           ()))))

;this one has only one index and so only one bound hyp.  we'd prefer this one to fire first
;see also bv-array-read-of-bv-array-write-same-better-work-hard
(defthmd bv-array-read-of-bv-array-write-same-better
  (implies (and (< index len)
                (natp width2)
                (<= width width2)
                (posp len)
                (natp index))
           (equal (bv-array-read width len index (bv-array-write width2 len index val lst))
                  (bvchop width val)))
  :hints (("Goal" :use (:instance bv-array-read-of-bv-array-write-both-better (index1 index) (index2 index))
           :in-theory (disable bv-array-read-of-bv-array-write-both-better))))

 ;;Do not remove.  This helps justify te correctness of the translation to STP.
;a read out of bounds returns 0
;note that the index is chopped down before the comparison
(defthmd bv-array-read-when-index-is-too-large
  (implies (and (<= len (bvchop (ceiling-of-lg len) index))
                (natp len))
           (equal (bv-array-read width len index data)
                  0))
  :hints (("Goal" :in-theory (e/d (bv-array-read) ()))))

;splits into cases
;does not require that the indices be in bounds
;special case for powers of 2?
;what if the lens are not equal?
(defthm bv-array-read-of-bv-array-write
  (implies (and (<= width2 width1) ;handle better?
                (integerp len)
                (natp width2)
                (integerp width1))
           (equal (bv-array-read width1 len index1 (bv-array-write width2 len index2 val lst))
                  (if (equal (bvchop (ceiling-of-lg len) index1)
                             (bvchop (ceiling-of-lg len) index2))
                      (if (< (bvchop (ceiling-of-lg len) index1) len)
                          (bvchop width2 val)
                        ;;out of bounds read is 0:
                        0)
                    (bv-array-read width2 len index1 lst))))
  :hints (("Goal" :in-theory (e/d (bvchop-when-i-is-not-an-integer
                                   ceiling-of-lg
                                   bv-array-write
                                   bv-array-read update-nth2)
                                  ()))))

(defthm bv-array-read-when-not-integerp-arg1-cheap
  (implies (not (integerp element-size))
           (equal (bv-array-read element-size len index data)
                  0))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable bv-array-read))))

(defthm bv-array-read-of-bv-array-write-same-width
  (implies (integerp len)
           (equal (bv-array-read width len index1 (bv-array-write width len index2 val lst))
                  (if (equal (bvchop (ceiling-of-lg len) index1)
                             (bvchop (ceiling-of-lg len) index2))
                      (if (< (bvchop (ceiling-of-lg len) index1) len)
                          (bvchop width val)
                        ;;out of bounds read is 0:
                        0)
                    (bv-array-read width len index1 lst))))
  :hints (("Goal" :use (:instance bv-array-read-of-bv-array-write
                                  (width1 (nfix width))
                                  (width2 (nfix width)))
           :in-theory (disable BV-ARRAY-READ-OF-BV-ARRAY-WRITE)
           )))

;one should instruct the rewriter to try this rule before the one above..
;don't have to worry about the out of bounds read case when len is a power of 2 (the chopped index will always be in bounds)
(defthm bv-array-read-of-bv-array-write-when-len-is-a-power-of-2
  (implies (and (power-of-2p len)
                (<= width2 width1) ;handle better?
                (integerp len)
                (natp width2)
                (integerp width1))
           (equal (bv-array-read width1 len index1 (bv-array-write width2 len index2 val lst))
                  (if (equal (bvchop (ceiling-of-lg len) index1)
                             (bvchop (ceiling-of-lg len) index2))
                      (bvchop width2 val)
                    (bv-array-read width2 len index1 lst))))
  :hints (("Goal" :in-theory (e/d (power-of-2p ceiling-of-lg) (bv-array-read bv-array-write)))))

(defthm bv-array-clear-of-repeat-same
  (equal (bv-array-clear 8 len start (repeat len 0))
         (repeat len 0))
  :hints (("Goal" :in-theory (e/d (update-nth-when-equal-of-nth
                                   bv-array-clear
                                   bv-array-write ;fixme
                                   update-nth2
                                   )
                                  ()))))

(defthm bv-array-clear-range-of-repeat-same
  (equal (bv-array-clear-range '8 len start end (repeat len 0))
         (repeat len 0))
  :hints (("Goal" :in-theory (enable bv-array-clear-range))))

;restrict to constants?
(defthm bv-array-clear-range-of-zeros
  (implies (and (all-equal$ 0 data)
                (true-listp data)
                (equal len (len data)))
           (equal (bv-array-clear-range '8 len start end data)
                  data))
  :hints (("Goal" :use (:instance bv-array-clear-range-of-repeat-same)
           :in-theory (e/d (ALL-EQUAL$-WHEN-TRUE-LISTP)
                           (bv-array-clear-range-of-repeat-same)))))

;move
(defthm equal-of-bv-array-write-of-1
  (equal (equal k (bv-array-write size 1 index val data))
         (and (true-listp k)
              (equal 1 (len k))
              (equal (car k) (bvchop size val))))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (e/d (bv-array-write update-nth2 UPDATE-NTH)
                           ( ;update-nth-becomes-update-nth2-extend-gen
                            ;LIST::UPDATE-NTH-EQUAL-REWRITE
                            ;LIST::UPDATE-NTH-EQUAL-UPDATE-NTH-REWRITE
                            )))))

;move
(defthm equal-of-bv-array-write-of-1-constant-version
  (implies (syntaxp (quotep k))
           (equal (equal k (bv-array-write size 1 index val data))
                  (and (true-listp k)
                       (equal 1 (len k))
                       (equal (car k) (bvchop size val)))))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (e/d (bv-array-write update-nth2 UPDATE-NTH)
                           ( ;update-nth-becomes-update-nth2-extend-gen
                            ;LIST::UPDATE-NTH-EQUAL-REWRITE
                            ;LIST::UPDATE-NTH-EQUAL-UPDATE-NTH-REWRITE
                            )))))

(defthm bv-array-clear-1-0
  (equal (bv-array-clear width 1 0 data)
         '(0))
  :hints (("Goal" :in-theory (e/d (bv-array-clear update-nth2 ;list::clear-nth
                                                  )
                                  (;LIST::UPDATE-NTH-BECOMES-CLEAR-NTH
;LIST::UPDATE-NTH-EQUAL-REWRITE
                                   )))))

(defthm bv-array-read-of-bv-array-write-too-narrow-cheap
  (implies (and (syntaxp (and (quotep len)
                              (quotep index)
                              (quotep len2)))
                (<= len2 index) ;means the write is too narrow
                (< index len)   ;work-hard?
                (natp index)
                (natp len)
                (natp len2)
                )
           (equal (bv-array-read width len index (bv-array-write width2 len2 index2 val data))
                  0))
  :hints (("Goal" ;:cases ((< index len))
           :in-theory (e/d (bv-array-read-opener bv-array-write BV-ARRAY-READ-WHEN-INDEX-IS-TOO-LARGE)
                           ( ;BVCHOP-OF-NTH-BECOMES-BV-ARRAY-READ
;GETBIT-OF-NTH-BECOMES-BV-ARRAY-READ
;NTH-BECOMES-BV-ARRAY-READ2
                            )))))

(defthm bvchop-list-of-repeat-of-nil
  (equal (bvchop-list n (repeat m nil))
         (repeat m 0))
  :hints (("Goal" :in-theory (e/d (bvchop-list repeat) (cons-onto-repeat
                                                         )))))

(defthm bv-array-write-of-bv-array-write-same-index
  (implies (and (< index len)
                (natp index)
                (natp len)
                (natp element-size)
                )
           (equal (bv-array-write element-size len index val1 (bv-array-write element-size len index val2 lst))
                  (bv-array-write element-size len index val1 lst)))
  :hints (("Goal" :in-theory (enable update-nth2 bv-array-write))))

;fixme can loop?
(defthmd bv-array-write-of-bv-array-write-diff
  (implies (and ;this is implied by them being unequal nats both of which are in bounds:
            (not (equal (bvchop (integer-length (+ -1 len)) index1)
                        (bvchop (integer-length (+ -1 len)) index2)))
;                (< index1 len)
;                (< index2 len)
            (natp index1)
            (natp index2)
;                (natp len)
;                (natp element-size)
            )
           (equal (bv-array-write element-size len index1 val1 (bv-array-write element-size len index2 val2 lst))
                  (bv-array-write element-size len index2 val2 (bv-array-write element-size len index1 val1 lst))
                  ))
  :hints (("Goal"
           :cases ((equal (bvchop (integer-length (+ -1 len))
                                   index2)
                          (bvchop (integer-length (+ -1 len))
                                   index1)))
           :in-theory (enable update-nth2 ;list::update-nth-update-nth-diff
                              ceiling-of-lg
                              ;list::update-nth-update-nth-diff
                              bv-array-write))))

;would like this not to mention len, but we have to know that the indices (after trimming down to the number of bits indicated by len) are in fact different.
(defthm bv-array-write-of-bv-array-write-diff-constant-indices
  (implies (and (syntaxp (quotep index1))
                (syntaxp (quotep index2))
                (< index2 index1)
                (< index1 len)
                (< index2 len)
                (natp index1)
                (natp index2)
;                (natp len) ;drop?
                )
           (equal (bv-array-write element-size len index1 val1 (bv-array-write element-size len index2 val2 lst))
                  (bv-array-write element-size len index2 val2 (bv-array-write element-size len index1 val1 lst))
                  ))
  :hints (("Goal" :use (:instance bv-array-write-of-bv-array-write-diff)
           :cases ((not (natp len)))
           :in-theory (disable bv-array-write-of-bv-array-write-diff))))

;subsumes the one for <
;seems gross
(defthmd take-when-<=-of-len
  (implies (<= (len x) n) ;expensive?
           (equal (take n x)
                  (if (zp n)
                      nil
                    (append x (repeat (- (nfix n) (len x)) nil)))))
  :hints
  (("Goal"
    :in-theory (e/d (take ;list::nth-append
                     )
                    (;take-of-cdr-becomes-subrange
                     )))))

(local
 (defthm arith-hack
   (equal (+ (- LEN) x (* 2 LEN))
          (+ len x))))

;move
(defthmd bvchop-list-of-take-of-bvchop-list-gen
  (implies (and (<= size2 size1)
                (natp size1)
                (natp size2))
           (equal (bvchop-list size1 (take len (bvchop-list size2 lst)))
                  (bvchop-list size2 (take len lst))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable take bvchop-list))))

;fixme think about how this interacts with the tightening rules...
(defthm bv-array-write-of-bv-array-write-diff-constant-indices-gen
  (implies (and (syntaxp (quotep index1))
                (syntaxp (quotep index2))
                (< index2 index1) ;only do it when the indices are out of order
                (<= element-size2 element-size1) ;the outer size is bigger
                (< index1 len)
                (< index2 len)
                (natp index1)
                (natp index2)
                (natp len)
                (natp element-size1)
                (natp element-size2)
                )
           (equal (bv-array-write element-size1 len index1 val1 (bv-array-write element-size2 len index2 val2 lst))
                  (bv-array-write element-size1 len index2 (bvchop element-size2 val2)
;the bvchop-list should have no affect when lst is a bv-array-write nest with element-size2
                                  (bv-array-write element-size1 len index1 val1 (bvchop-list element-size2 lst)))))
  :hints
  (("Goal" :cases ( (<= len (len lst)))
    :in-theory (e/d (update-nth2 bv-array-write-opener ;list::update-nth-update-nth-diff
                                 bvchop-list-of-take-of-bvchop-list-gen
                                 )
                    (;LIST::UPDATE-NTH-EQUAL-REWRITE
                     BVCHOP-LIST-OF-TAKE)))))

;allows the widths to differ (so we don't have to tighten the write nest first)
(defthm bv-array-read-of-bv-array-write-same-gen
  (implies (and (<= width1 width2)
                (< index len)
                (natp width1)
                (integerp width2)
                (natp index)
                (integerp len))
           (equal (bv-array-read width1 len index (bv-array-write width2 len index val lst))
                  (bvchop width1 val)))
  :hints (("Goal" :in-theory (e/d (bv-array-read bv-array-write)
                                  ()))))


;; ;drop?
;; (defthm endp-of-bv-array-write
;;   (equal (endp (bv-array-write esize len index val lst))
;;          (zp len))
;;   :hints (("Goal" :in-theory (enable update-nth2 bv-array-write))))

(defthm bv-array-read-when-element-size-is-0
  (equal (bv-array-read 0 len index data)
         0)
  :hints (("Goal" :in-theory (e/d (bv-array-read) (;NTH-OF-BV-ARRAY-WRITE-BECOMES-BV-ARRAY-READ
                                                   )))))

(defthmd nth-of-bv-array-write-becomes-bv-array-read
  (implies (and (< n len)
                (natp n)
                (natp len))
           (equal (nth n (bv-array-write esize len index val data))
                  (bv-array-read esize len n (bv-array-write esize len index val data))))
  :hints (("Goal" :in-theory (enable BV-ARRAY-READ update-nth2 bv-array-write ceiling-of-lg))))

(theory-invariant (incompatible (:definition bv-array-read) (:rewrite nth-of-bv-array-write-becomes-bv-array-read)))

(defthm bv-array-read-of-nil
  (equal (bv-array-read width len index nil)
         0)
  :hints (("Goal" :in-theory (e/d (bv-array-read) ()))))

(defthm bv-array-read-of-0-arg2
  (equal (bv-array-read size 0 index data)
         0)
  :hints (("Goal" :in-theory (e/d (bv-array-read) ()))))

;; Make an empty array containing LEN zeros.  Element-size is included so you
;; can tell from the call what the type of the elements is.
(defun empty-bv-array (element-size len)
  (declare (ignore element-size))
  (repeat len 0))

;if you are xoring 2 array lookups with the same index, you can instead just do
;one lookup in the XOR of the arrays (only makes sense if the arrays are constants)
(defthm bitxor-of-bv-array-read-and-bv-array-read-constant-arrays
  (implies (and (syntaxp (quotep vals1))
                (syntaxp (quotep vals2))
                (equal 256 (len vals1))
                (equal 256 (len vals2))
                )
           (equal (bitxor (bv-array-read 1 256 index vals1)
                          (bv-array-read 1 256 index vals2))
                  (bv-array-read 1 256 index (bvxor-list 1 vals1 vals2))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
;          :induct (sub1-cdr-cdr-induct index vals1 vals2)
           :in-theory (e/d (BV-ARRAY-READ ;nth
                            )
                           (;NTH-BECOMES-BV-ARRAY-READ2 GETBIT-OF-NTH-BECOMES-BV-ARRAY-READ BVCHOP-OF-NTH-BECOMES-BV-ARRAY-READ
                            ;;BITXOR-OF-NTH-ARG1
                            ;;BITXOR-OF-NTH-ARG2
                            ;;NTH-OF-CDR
                            )))))

(defthm bitxor-of-bv-array-read-and-bv-array-read-constant-arrays-alt
  (implies (and (syntaxp (quotep vals1))
                (syntaxp (quotep vals2))
                (equal 256 (len vals1))
                (equal 256 (len vals2))
                )
           ;; index must be the same for both reads:
           (equal (bitxor (bv-array-read 1 256 index vals1)
                          (bitxor (bv-array-read 1 256 index vals2)
                                  otherval))
                  (bitxor (bv-array-read 1 256 index (bvxor-list 1 vals1 vals2))
                          otherval)))
  :hints (("Goal" :use (:instance bitxor-of-bv-array-read-and-bv-array-read-constant-arrays)
           :in-theory (disable bitxor-of-bv-array-read-and-bv-array-read-constant-arrays))))

;move
;; breaks the abstraction
(defthm car-of-bv-array-write
  (implies (and (<= 1 len)
                (integerp len)
                (< key len)
                ;(natp len)
                (natp key))
           (equal (car (bv-array-write element-size len key val lst))
                  (if (< key 1)
                      (bvchop element-size val)
                    (bvchop element-size (car lst)))))
  :hints (("Goal" :in-theory (e/d (bv-array-write-opener update-nth2) ()))))

;move
(defthm car-of-bv-array-write-gen
  (implies (posp len)
           (equal (car (bv-array-write element-size len key val lst))
                  (if (equal 0 (bvchop (ceiling-of-lg len) key))
                      (bvchop element-size val)
                    (bvchop element-size (car lst)))))
  :hints (("Goal" :expand (bv-array-write element-size len key val lst)
           :in-theory (enable update-nth2))))

(defthm bvchop-list-of-update-nth2
  (implies (and (< key len)
                ;(<= len (+ 1 (len lst)))
                (<= len (len lst)) ;new
                (integerp len)
                (natp key))
           (equal (bvchop-list size (update-nth2 len key val lst))
                  (update-nth2 len key (bvchop size val) (bvchop-list size lst))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (update-nth2 update-nth
                                        bvchop-list) (;LIST::UPDATE-NTH-EQUAL-REWRITE
                                                      )))))

;move
(defthm bv-array-write-of-logext-around-value
  (implies (and (<= element-size size)
                (< key len)
                (natp size)
                (natp element-size)
                (natp len)
                (natp key)
                )
           (equal (bv-array-write element-size len key (logext size val) lst)
                  (bv-array-write element-size len key val lst)))
  :hints (("Goal" :in-theory (e/d (update-nth2 bv-array-write) (logext)))))

;; (defthm bvchop-list-of-take-of-logext-list
;;   (implies (and (<= element-size size)
;;                 (natp size)
;;                 (natp element-size))
;;            (equal (bvchop-list element-size (take len (logext-list size lst)))
;;                   (bvchop-list element-size (take len lst))))
;;   :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;            :in-theory (e/d (bvchop-list-definition logext-list take list::nth-with-large-index)
;;                            (TAKE-OF-CDR-BECOMES-SUBRANGE)))))

;; (defthm bv-array-write-of-logext-list
;;   (implies (and (<= element-size size)
;;                 (< key len)
;;                 (natp size)
;;                 (natp element-size)
;;                 (natp len)
;;                 (natp key))
;;            (equal (bv-array-write element-size len key val (logext-list size lst))
;;                   (bv-array-write element-size len key val lst)))
;;   :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;            :in-theory (e/d (update-nth2 logext-list-of-cdr bv-array-write)
;;                            (logext-list cdr-of-logext-list)))))

;; ;move
;; (theory-invariant (incompatible (:rewrite nthcdr-of-true-list-fix) (:rewrite true-list-fix-of-nthcdr)))

;matches std except has one less nfix
(defthm nthcdr-of-update-nth-simpler
  (equal (nthcdr n1 (update-nth n2 val x))
         (if (< (nfix n2) (nfix n1))
             (nthcdr n1 x)
           (update-nth (- n2 (nfix n1)) val (nthcdr n1 x))))
  :hints (("Goal" ;:induct (sub1-sub1-cdr-induct n key l)
           :expand (UPDATE-NTH n2 VAL (NTHCDR (+ -1 N1) (CDR x)))
           :in-theory (enable update-nth nthcdr))))

(defthm nthcdr-of-bv-array-write
  (implies (and (<= n (len lst))
                (equal (len lst) len) ;bozo
                (< key len)           ;Mon Jul 19 20:28:02 2010
                (natp n)
                (natp key))
           (equal (nthcdr n (bv-array-write element-size len key val lst))
                  (if (< key n)
                      (bvchop-list element-size (nthcdr n (true-list-fix lst)))
                    (bv-array-write element-size (- len n) (- key n) val (nthcdr n lst)))))
  :hints (("Goal" :in-theory (e/d (UPDATE-NTH2 bv-array-write ceiling-of-lg NTHCDR-of-true-list-fix)
                                  (;LIST::FIX-OF-NTHCDR
                                   )))))



(defthm nthcdr-of-bv-array-write-better
  (implies (and (<= n len)
                (integerp len)
;(natp len)
                (< key len)
                (natp n)
                (natp key))
           (equal (nthcdr n (bv-array-write element-size len key val lst))
                  (if (< key n)
                      (bvchop-list element-size (nthcdr n (take len (true-list-fix lst))))
                    (bv-array-write element-size (- len n) (- key n) val (nthcdr n lst)))))
  :hints (("Goal"
           :cases ((< key n))
           :in-theory (e/d (update-nth2 bv-array-write-opener)
                           (
;                            LIST::UPDATE-NTH-EQUAL-REWRITE
                            )))))

;todo: use in the JVM model
(defund array-of-zeros (width len)
  (declare (ignore width)
           (xargs :guard (natp len)))
  (repeat len 0))

(defthm len-of-array-of-zeros
  (equal (len (array-of-zeros width len))
         (nfix len))
  :hints (("Goal" :in-theory (enable array-of-zeros))))

(defthm all-unsigned-byte-p-of-array-of-zeros
  (implies (natp width)
           (all-unsigned-byte-p width (array-of-zeros width len)))
  :hints (("Goal" :in-theory (enable array-of-zeros))))

(defthm nthcdr-of-array-of-zeros
  (implies (natp n)
           (equal (nthcdr n (array-of-zeros width len))
                  (array-of-zeros width (- len n))))
  :hints (("Goal" :in-theory (enable array-of-zeros))))

;; Reading from an array of length 1 always gives the 0th element (and is in
;; fact independent from the index).
;drop this one?
(defthmd bv-array-read-of-1-arg2
  (equal (bv-array-read element-size 1 index data)
         (bvchop element-size (nth 0 data)))
  :hints (("Goal" :in-theory (enable bv-array-read))))

;; the index gets chopped down to 0 bits
;todo: maybe enable
(defthmd bv-array-read-of-1-arg2-better
  (implies (< 0 index) ;prevents loops (could also do a syntactic check against '0 but not for axe?)
           (equal (bv-array-read element-size 1 index data)
                  (bv-array-read element-size 1 0 data)))
  :hints (("Goal" :in-theory (e/d (bv-array-read) ()))))

(defthmd bv-array-write-of-bv-array-write-when-length-is-1
  (equal (bv-array-write size 1 index1 val1 (bv-array-write size 1 index2 val2 data))
         (bv-array-write size 1 0 val1 '(0))))

(defthmd bv-array-read-of-bv-array-write-when-length-is-1
  (equal (bv-array-read size 1 index1 (bv-array-write size 1 index2 val data))
         (bvchop size val))
  :hints (("Goal" :in-theory (enable BV-ARRAY-WRITE
                                     BV-ARRAY-READ))))



;;
;; bv-array-if
;;

(defund bv-array-if (element-size len test array1 array2)
  (declare (xargs :guard (and (natp len)
                              (natp element-size)
                              (true-listp array1)
                              (true-listp array2))))
  (if test
      (bvchop-list element-size (take len array1))
    (bvchop-list element-size (take len array2))))

(defthm bv-arrayp-of-bv-array-if
  (implies (and (natp element-size)
                (natp len))
           (bv-arrayp element-size len (bv-array-if element-size len test array1 array2)))
  :hints (("Goal" :in-theory (enable bv-array-if))))

(defthm bv-array-if-of-t
  (equal (bv-array-if element-size len t array1 array2)
         (bvchop-list element-size (take len array1)))
  :hints (("Goal" :in-theory (enable bv-array-if))))

(defthm bv-array-if-of-nil
  (equal (bv-array-if element-size len nil array1 array2)
         (bvchop-list element-size (take len array2)))
  :hints (("Goal" :in-theory (enable bv-array-if))))

(defund bind-var-to-bv-array-length (var term)
  (declare (xargs :guard (and (symbolp var)
                              (pseudo-termp term))
                  :guard-hints (("Goal" :in-theory (enable memberp-of-cons-when-constant)))))
  (if (variablep term)
      nil ;fail
    (if (and (quotep term)
             (true-listp term))
        (acons var `',(len term) nil)
      (let ((fn (ffn-symb term)))
        (if (and (member-eq fn '(bv-array-write bv-array-if))
                 (quotep (farg2 term))
                 (natp (unquote (farg2 term))))
            (acons var (farg2 term) nil)
          nil)))))

(defund bind-var-to-bv-array-element-size (var term)
  (declare (xargs :guard (and (symbolp var)
                              (pseudo-termp term))
                  :guard-hints (("Goal" :in-theory (enable memberp-of-cons-when-constant)))))
  (if (variablep term)
      nil ;fail
    (if (and (quotep term)
             (true-listp term)
             (all-integerp term))
        (acons var `',(width-of-widest-int term) nil)
      (let ((fn (ffn-symb term)))
        (if (and (member-eq fn '(bv-array-write bv-array-if))
                 (quotep (farg1 term))
                 (natp (unquote (farg1 term))))
            (acons var (farg1 term) nil)
          nil)))))

(defthmd if-becomes-bv-array-if
  (implies (and (bind-free (bind-var-to-bv-array-length 'lenx x) (lenx))
                (bind-free (bind-var-to-bv-array-length 'leny y) (leny))
                (bind-free (bind-var-to-bv-array-element-size 'element-sizex x) (element-sizex))
                (bind-free (bind-var-to-bv-array-element-size 'element-sizey y) (element-sizey))
                (equal element-sizex element-sizey) ;gen (take the larger?)
                (equal lenx leny)
                (bv-arrayp element-sizex lenx x) ;make a -forced version?
                (bv-arrayp element-sizey leny y) ;make a -forced version?
                )
           (equal (if test x y)
                  (bv-array-if element-sizex lenx test x y)))
  :hints (("Goal" :in-theory (enable bv-array-if))))

(defthmd myif-becomes-bv-array-if
  (implies (and (bind-free (bind-var-to-bv-array-length 'lenx x) (lenx))
                (bind-free (bind-var-to-bv-array-length 'leny y) (leny))
                (bind-free (bind-var-to-bv-array-element-size 'element-sizex x) (element-sizex))
                (bind-free (bind-var-to-bv-array-element-size 'element-sizey y) (element-sizey))
                (equal element-sizex element-sizey) ;gen (take the larger?)
                (equal lenx leny)
                (bv-arrayp element-sizex lenx x) ;make a -forced version?
                (bv-arrayp element-sizey leny y) ;make a -forced version?
                )
           (equal (myif test x y)
                  (bv-array-if element-sizex lenx test x y)))
  :hints (("Goal" :in-theory (enable bv-array-if))))

;test:
;; (thm
;;  (equal x (if test
;;               (bv-array-write 8 2 x y z)
;;             (bv-array-write 8 2 w v u)))
;;  :hints (("Goal" :in-theory (enable if-becomes-bv-array-if))))

(defthm bv-arrayp-of-bv-array-write
  (implies (and (natp element-size)
                (natp len))
           (bv-arrayp element-size len (bv-array-write ELEMENT-SIZE LEN INDEX VAL DATA)))
  :hints (("Goal" :in-theory (enable bv-array-write))))

;; (defthm bv-array-write-of-logext-list-better
;;   (implies (and (<= element-size size)
;;                 (natp size)
;;                 (natp element-size)
;;                 (natp len)
;;                 (natp key))
;;            (equal (bv-array-write element-size len key val (logext-list size lst))
;;                   (bv-array-write element-size len key val lst)))
;;   :otf-flg t
;;   :hints (("Goal" :cases ((< key len))
;;            :use ((:instance bvchop-list-of-take-of-bvchop-list
;;                            (size element-size)
;;                            (lst (logext-list size lst)))
;;                  (:instance bvchop-list-of-take-of-bvchop-list
;;                            (size element-size)
;;                            (lst lst)))
;;            :in-theory (e/d (bv-array-write update-nth2) (bvchop-list-of-take-of-bvchop-list
;;                                                          ;UPDATE-NTH-BECOMES-UPDATE-NTH2-EXTEND-GEN
;;                                                          )))))

;; (DEFTHM BV-ARRAY-READ-OF-LOGEXT-LIST-better
;;   (IMPLIES (AND (<= SIZE SIZE2)
;;                 (EQUAL LEN (LEN LST))
;;                 (NATP INDEX)
;;                 (NATP LEN)
;;                 (NATP SIZE)
;;                 (INTEGERP SIZE2))
;;            (EQUAL (BV-ARRAY-READ SIZE LEN INDEX (LOGEXT-LIST SIZE2 LST))
;;                   (BV-ARRAY-READ SIZE LEN INDEX LST)))
;;   :otf-flg t
;;   :HINTS
;;   (("Goal" :cases ((< INDEX (LEN LST)))
;;     :IN-THEORY (E/d (BVCHOP-WHEN-I-IS-NOT-AN-INTEGER
;;                        BV-ARRAY-READ) (NTH-OF-BV-ARRAY-WRITE-BECOMES-BV-ARRAY-READ)))))

;; Chops down the index if needed
(defthm bv-array-read-when-index-is-too-high
  (implies (and (syntaxp (and (quotep len)
                              (quotep index)))
                (not (unsigned-byte-p (ceiling-of-lg len) index))) ;prevents loops
           (equal (bv-array-read width len index arr)
                  (bv-array-read width len (bvchop (ceiling-of-lg len) index) arr)))
  :hints (("Goal" :in-theory (e/d (bv-array-read)
                                  ()))))

;; Replaces myif with bv-array-if
(defthm bv-array-write-of-myif
  (implies (and (natp len)
                (natp width)
                (natp index))
           (equal (bv-array-write width len index val (myif test arr1 arr2))
                  (bv-array-write width len index val (bv-array-if width len test arr1 arr2))))
  :hints (("Goal" :in-theory (e/d (bv-array-if bv-array-write update-nth2)
                                  ()))))

(defthm bv-arrayp-of-myif
  (equal (bv-arrayp element-width length (myif test val1 val2))
         (if test
             (bv-arrayp element-width length val1)
           (bv-arrayp element-width length val2))))

(defthm len-of-bv-array-if
  (equal (len (bv-array-if element-size len test array1 array2))
         (nfix len))
  :hints (("Goal" :in-theory (enable bv-array-if))))

(defthm consp-of-bv-array-if
  (equal (consp (bv-array-if element-size len test array1 array2))
         (posp len))
  :hints (("Goal" :in-theory (enable bv-array-if))))

;for axe
(defthm bv-arrayp-constant-opener
  (implies (syntaxp (and (quotep element-width)
                         (quotep length)
                         (quotep val)))
           (equal (bv-arrayp element-width length val)
                  (and (all-unsigned-byte-p element-width val)
                       (true-listp val)
                       (equal (len val) length)))))

;for axe
;maybe not needed since the test will let us resolve it?
(defthm bv-array-if-constant-opener
  (implies (syntaxp (and (quotep test)
                         (quotep element-size)
                         (quotep len)
                         (quotep array1)
                         (quotep array2)))
           (equal (bv-array-if element-size len test array1 array2)
                  (if test
                      (bvchop-list element-size (take len array1))
                      (bvchop-list element-size (take len array2)))))
  :hints (("Goal" :in-theory (enable bv-array-if))))

;todo: allow len to differ and allow element-size to differ
(defthm bv-array-read-of-bv-array-if
  (equal (bv-array-read element-size len index (bv-array-if element-size len test arr1 arr2))
         (bvif element-size
               test
               (bv-array-read element-size len index arr1)
               (bv-array-read element-size len index arr2)))
  :hints (("Goal" :in-theory (enable bv-array-if BV-ARRAY-READ))))

;; Lift the if through bv-array-write
(defthm bv-array-write-of-bv-array-if
  (equal (bv-array-write element-size len index val (bv-array-if element-size len test arr1 arr2))
         (bv-array-if element-size
                      len
                      test
                      (bv-array-write element-size len index val arr1)
                      (bv-array-write element-size len index val arr2)))
  :hints (("Goal" :in-theory (enable bv-array-if bv-array-write update-nth2 take-when-zp))))

(defthm bv-array-if-of-0-arg2
  (equal (bv-array-if element-size 0 test array1 array2)
         nil)
  :hints (("Goal" :in-theory (enable bv-array-if))))

;can lose type info?
(defthm bv-array-if-same-branches
  (equal (bv-array-if element-size len test array array)
         (bvchop-list element-size (take len array)))
  :hints (("Goal" :in-theory (enable bv-array-if))))

;can lose explicit type info
;could restrict to constant arrays...
(defthm bv-array-if-same-branches-safe
  (implies (and (bv-arrayp element-size len array)
                (natp len))
           (equal (bv-array-if element-size len test array array)
                  array))
  :hints (("Goal" :in-theory (enable bv-array-if))))

;; This passes through the CAR.  We could instead use BV-ARRAY-READ
(defthm car-of-bv-array-if
  (implies (posp len)
           (equal (car (bv-array-if element-size len test array1 array2))
                  (bvif element-size test (car array1) (car array2))))
  :hints (("Goal" :in-theory (enable bv-array-if))))

;; This passes through the CDR.
(defthm cdr-of-bv-array-if
  (implies (posp len)
           (equal (cdr (bv-array-if element-size len test array1 array2))
                  (bv-array-if element-size (+ -1 len) test (cdr array1) (cdr array2))))
  :hints (("Goal" :in-theory (enable bv-array-if))))

(defthm cdr-of-bv-array-if-2
  (implies (and (bv-arrayp element-size len array1)
                (bv-arrayp element-size len array2))
           (equal (cdr (bv-array-if element-size len test array1 array2))
                  (if test
                      (cdr array1)
                    (cdr array2))))
  :hints (("Goal" :in-theory (enable bv-array-if))))

(defthmd nth-of-bv-array-if
  (implies (and (< n len)
                (natp n)
                (natp len))
           (equal (nth n (bv-array-if element-size len test array1 array2))
                  (bvif element-size test (nth n array1) (nth n array2))))
  :hints (("Goal" :in-theory (enable bv-array-if))))

;; Rules about treating bv-array-if as a list:
(defun bv-array-if-list-rules ()
  '(consp-of-bv-array-if
    car-of-bv-array-if
    cdr-of-bv-array-if
    nth-of-bv-array-if))

;; helps to resolve the size of the array, for translation to STP
(defthm bv-array-read-of-bvif-arg2
  (equal (bv-array-read element-size (bvif size2 test len1 len2) index data)
         (bvif element-size
               test
               (bv-array-read element-size (bvchop size2 len1) index data)
               (bv-array-read element-size (bvchop size2 len2) index data)))
  :hints (("Goal" :in-theory (enable boolif bvif))))

(defthm bv-array-write-of-bv-array-read
  (implies (and (natp len)
                (natp index)
                (< index (len arr)))
           (equal (bv-array-write element-size len index (bv-array-read element-size len index arr) arr)
                  (bvchop-list element-size (take len arr))))
  :hints (("Goal" :in-theory (enable bv-array-write bv-array-read update-nth2 update-nth-when-equal-of-nth))))

;disable?
(defthm myif-of-bv-array-write-arg2
  (implies (and (all-unsigned-byte-p element-size thenpart)
                (natp key)
                (equal len (len lst))
                (< key len)
                (natp element-size)
                (equal len (len thenpart))
                (true-listp thenpart)
                )
           (equal (myif test thenpart (bv-array-write element-size len key val lst))
                  (bv-array-write element-size
                                  len
                                  key
                                  (myif test (bv-array-read element-size len key thenpart) val)
                                  (myif test thenpart lst))))
  :hints (("Goal" :in-theory (e/d (myif ;update-nth2 ;bv-array-read bv-array-write
                                        )
                                  (nth-0-cons ;myif-of-constant-lists
                                   ;LIST::UPDATE-NTH-EQUAL-REWRITE
                                   )))))

;disable?
(defthm myif-of-bv-array-write-arg1
  (implies (and (all-unsigned-byte-p element-size thenpart)
                (natp key)
                (equal len (len lst))
                (< key len)
                (natp element-size)
                (equal len (len thenpart))
                (true-listp thenpart)
                )
           (equal (myif test (bv-array-write element-size len key val lst) thenpart)
                  (bv-array-write element-size
                                 len
                                 key
                                 (myif test val (bv-array-read element-size len key thenpart))
                                 (myif test lst thenpart))))
  :hints (("Goal" :in-theory (e/d (myif update-nth2 bv-array-read bv-array-write update-nth-when-equal-of-nth)
                                  (nth-0-cons ;myif-of-constant-lists
                                   )))))

;use a trim rule?
(defthm bv-array-write-of-bvxor
  (implies (and (< element-size size)
                (< key len)
                (natp size)
                (natp element-size)
                (natp len)
                (natp key)
                )
           (equal (bv-array-write element-size len key (bvxor size val val2) lst)
                  (bv-array-write element-size len key (bvxor element-size val val2) lst)))
  :hints (("Goal" :in-theory (e/d (update-nth2 bv-array-write) (;TAKE-OF-CDR-BECOMES-SUBRANGE
                                                                )))))

;drop the getbit?
(defthm array-reduction-0-1
  (equal (bv-array-read 1 2 index '(0 1))
         (getbit 0 (ifix index)))
  :hints (("Goal"
           :in-theory (e/d (bv-array-read ;LIST::NTH-OF-CONS
                            GETBIT-WHEN-VAL-IS-NOT-AN-INTEGER
                            NTH-OF-CONS)
                           ()))))

(defthm array-reduction-when-all-same
  (implies (and (equal data (repeat (len data) (car data))) ;expensive to check?
                (natp index)
                (< index len)
                (equal (len data) len)
                (true-listp data)
                (all-unsigned-byte-p element-size data) ;drop?
                )
           (equal (bv-array-read element-size len index data)
                  (bv-array-read element-size len 0 data) ;
                  ;(bvchop element-size (car data))
                  ))
  :hints (("Goal"
           :in-theory (e/d (bv-array-read ;LIST::NTH-OF-CONS
                                   )
                           ()))))

(defthm all-unsigned-byte-p-of-bv-array-write-gen-2
  (implies (and (< size element-size) ;not logically necessary, but keeps us from wasting time on this rule when the regular rule would suffice (BOZO ensure that one fires first?)
                (all-unsigned-byte-p size lst)
                (unsigned-byte-p size val)
                (equal len (len lst))
                (true-listp lst)
                (natp key)
                (< key len)
                (natp size)
                (natp element-size))
           (equal (all-unsigned-byte-p size (bv-array-write element-size len key val lst))
                  t))
  :hints (("Goal" :in-theory (enable update-nth2 bv-array-write))))

;more like this? or a general rule?
(defthm getbit-of-bv-array-read-too-high
  (implies (and (<= m n)
                (integerp n)
                (natp m))
           (equal (getbit n (bv-array-read m len index data))
                  0))
  :hints (("Goal" :in-theory (enable GETBIT-TOO-HIGH))))

(defthm take-of-bv-array-write
  (implies (and (<= n (len lst))
                (equal (len lst) len) ;bozo
                (natp n)
                (< key len) ;Mon Jul 19 20:28:02 2010
                (natp key))
           (equal (take n (bv-array-write element-size len key val lst))
                  (if (< key n)
                      (bv-array-write element-size n key val (take n lst))
                    (BVCHOP-LIST ELEMENT-SIZE (TAKE N LST)))))
  :hints (("Goal" :in-theory (enable UPDATE-NTH2 bv-array-write ceiling-of-lg))))

;see <-LEMMA-FOR-KNOWN-OPERATORS-NON-DAG
;bozo gen
(defthm bv-array-read-numeric-bound
  (< (bv-array-read 8 len index data) 256)
  :hints (("Goal" :in-theory (enable bv-array-read))))

(defthm myif-of-bv-array-read-becomes-bvif-arg2
  (implies (and (unsigned-byte-p esize y)
                (natp esize))
           (equal (myif test y (bv-array-read esize len index x))
                  (bvif esize test y (bv-array-read esize len index x))))
  :hints (("Goal" :in-theory (enable myif bvif))))

(defthm myif-of-bv-array-read-becomes-bvif-arg1
  (implies (and (unsigned-byte-p esize y)
                (natp esize))
           (equal (myif test (bv-array-read esize len index x) y)
                  (bvif esize test (bv-array-read esize len index x) y)))
  :hints (("Goal" :in-theory (enable myif bvif))))

;this seems to be the magic rule (together with cons-a-onto-constant-size-1-becomes-bv-array-write perhaps) that lets us turn a cons nest into a bv-array-write-nest
(defthmd cons-of-bv-array-write
  (implies (and (unsigned-byte-p esize a)
                (natp len)
                (natp esize)
                (< index len)
                (natp index))
           (equal (cons a (bv-array-write esize len index b lst))
                  (bv-array-write esize (+ 1 len) 0 a (bv-array-write esize (+ 1 len) (+ 1 index) b (cons a lst)))
                  ))
  :hints (("Goal" :in-theory (enable update-nth2 bv-array-write ceiling-of-lg))))

;BOZO write a rule to allow width1 <= width2
(defthmd bv-array-read-of-bv-array-write-diff-safe-gen
  (implies (and (syntaxp (and (quotep index1)
                              (quotep index2)))
                (<= width2 width1)
                (natp width2)
                (integerp width1)
                (not (equal index1 index2))
                (natp index1)
                (natp index2)
                (< index1 len)
                (< index2 len)
                (integerp len))
           (equal (bv-array-read width1 len index1 (bv-array-write width2 len index2 val lst))
                  (bv-array-read width2 len index1 lst)))
  :hints
  (("Goal" :in-theory (e/d (bvchop-when-i-is-not-an-integer
                            BV-ARRAY-WRITE-opener
                            bv-array-read-opener update-nth2)
                           (NTH-OF-BV-ARRAY-WRITE-BECOMES-BV-ARRAY-READ
                            ARRAY-REDUCTION-WHEN-ALL-SAME)))))

(defthmd bv-array-write-when-data-isnt-an-all-unsigned-byte-p
  (implies (and (syntaxp (quotep data))
                (syntaxp (quotep esize))
                (not (all-unsigned-byte-p esize data))
                (equal (len data) len)
                (< INDEX (LEN DATA))
                (natp index)
                (true-listp data)
                (natp esize)
                (< 0 len))
           (equal (bv-array-write esize len index val data)
                  (bv-array-write esize len index val (bvchop-list esize data))))
  :hints
  (("Goal"
    :cases ((<= (len data) (bvchop isize index)))
    :in-theory (enable  bvchop-when-i-is-not-an-integer
                       BV-ARRAY-WRITE
                       UPDATE-NTH2
                       ;LIST::LEN-UPDATE-NTH-BETTER
                       ;;list::nth-with-large-index
                       ))))

;disable?
(defthm nth-of-bv-array-write-becomes-bv-array-read-strong
  (implies (natp len)
           (equal (nth n (bv-array-write esize len index val data))
                  (if (< (nfix n) len)
                      (if (natp n)
                          ;usual case:
                          (bv-array-read esize len n (bv-array-write esize len index val data))
                        (bv-array-read esize len 0 (bv-array-write esize len index val data)))
                    nil)))
  :hints (("Goal"
           :expand ((BV-ARRAY-READ ESIZE LEN 0 DATA))
           :in-theory (enable ;list::nth-with-large-index
                       bv-array-write
                       bv-array-read
                       nth-when-<=-len
                       natp))))
