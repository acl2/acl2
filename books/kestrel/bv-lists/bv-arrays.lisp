; Rules about bv-array operations
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/arithmetic-light/power-of-2p" :dir :system)
(include-book "bv-arrayp")
(include-book "bv-array-read")
;(include-book "array-of-zeros")
(include-book "bv-array-write")
(include-book "bv-array-if")
(include-book "append-arrays")
(include-book "width-of-widest-int")
(include-book "bvxor-list")
(include-book "kestrel/bv/bvif" :dir :system)
(include-book "kestrel/bv/bitxor" :dir :system)
(include-book "kestrel/bv/bitnot" :dir :system)
(include-book "kestrel/lists-light/repeat" :dir :system)
(include-book "kestrel/utilities/myif" :dir :system)
(include-book "kestrel/utilities/forms" :dir :system)
(include-book "ihs/basic-definitions" :dir :system) ;for logext, todo: use bv/logext-def
(include-book "kestrel/lists-light/all-equal-dollar" :dir :system)
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
(local (include-book "kestrel/arithmetic-light/expt2" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/arithmetic-light/integer-length2" :dir :system))
(local (include-book "kestrel/bv/unsigned-byte-p" :dir :system))
(local (include-book "kestrel/bv/logext" :dir :system))
(local (include-book "all-unsigned-byte-p2"))

;move
(in-theory (disable len))

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
           :in-theory (e/d (UPDATE-NTH2 len) (len-of-cdr)))))

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

;not true any more?
;; (defthm bv-array-write-when-index-not-positive-cheap
;;   (implies (< index 0)
;;            (equal (bv-array-write element-size len index val data)
;;                   (bv-array-write element-size len 0 val data)))
;;   :rule-classes ((:rewrite :backchain-limit-lst (0)))
;;   :hints (("Goal" :in-theory (enable bv-array-write update-nth2))))

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
  :hints (("Goal" :in-theory (enable bv-array-read-opener bv-array-write ceiling-of-lg))))

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
  (equal (bv-array-read elemement-width len index (bvchop-list elemement-width array))
         (bv-array-read elemement-width len index array))
  :hints (("Goal" :cases ((posp len))
           :in-theory (enable bv-array-read))))

;bozo combine these?
;drop some hyps?
;allow widths to differ?
(defthm bv-array-read-of-bvchop-list2
  (implies (and (natp width)
                (integerp len)
                (< index len)
                (natp index))
           (equal (bv-array-read width len index (bvchop-list width lst))
                  (bv-array-read width len index lst)))
  :hints (("Goal" :in-theory (enable NTH-WHEN-<=-LEN
                                     bv-array-read BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))))

(defthmd bv-array-read-when-data-isnt-an-all-unsigned-byte-p
  (implies (and (syntaxp (and (quotep data)
                              (quotep esize)))
                (not (all-unsigned-byte-p esize data)) ; gets computed
                (equal (len data) len)
                (natp esize)
                (< 0 len))
           (equal (bv-array-read esize len index data)
                  (bv-array-read esize len index (bvchop-list esize data))))
  :hints
  (("Goal"
    :cases ((<= (len data) (bvchop isize index)))
    :in-theory (enable bvchop-when-i-is-not-an-integer))))

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

(in-theory (disable bvchop-list)) ; move?

;see the better version below
(defthmd bv-array-read-of-bv-array-write-both
  (implies (and (equal len (len lst))
                (natp index1)
                (natp index2)
                (< index1 len)
                (< index2 len))
           (equal (bv-array-read width len index1 (bv-array-write width len index2 val lst))
                  (if (not (equal index1 index2))
                      (bv-array-read width len index1 lst)
                    (bvchop width val))))
  :hints (("Goal" :in-theory (enable bvchop-when-i-is-not-an-integer
                                     bv-array-read
                                     ceiling-of-lg
                                     bv-array-write))))

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
  :hints (("Goal" :in-theory (enable bvchop-when-i-is-not-an-integer
                                     ceiling-of-lg
                                     bv-array-read
                                     bv-array-write))))

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
  :hints (("Goal" :in-theory (enable bv-array-read))))

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
  :hints (("Goal" :in-theory (enable bvchop-when-i-is-not-an-integer
                                     ceiling-of-lg
                                     bv-array-write
                                     bv-array-read update-nth2))))

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
                (natp width2)
                (integerp width1))
           (equal (bv-array-read width1 len index1 (bv-array-write width2 len index2 val lst))
                  (if (equal (bvchop (ceiling-of-lg len) index1)
                             (bvchop (ceiling-of-lg len) index2))
                      (bvchop width2 val)
                    (bv-array-read width2 len index1 lst))))
  :hints (("Goal" :in-theory (e/d (power-of-2p ceiling-of-lg) (bv-array-read bv-array-write)))))

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
                           (;BVCHOP-OF-NTH-BECOMES-BV-ARRAY-READ
;GETBIT-OF-NTH-BECOMES-BV-ARRAY-READ
                            )))))

(defthm bvchop-list-of-repeat-of-nil
  (equal (bvchop-list n (repeat m nil))
         (repeat m 0))
  :hints (("Goal" :in-theory (e/d (bvchop-list repeat) (cons-onto-repeat)))))

;subsumes the one for <
;seems gross
(defthmd take-when-<=-of-len
  (implies (<= (len x) n) ;expensive?
           (equal (take n x)
                  (if (zp n)
                      nil
                    (append x (repeat (- (nfix n) (len x)) nil)))))
  :hints (("Goal" :in-theory (enable take))))

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
  :hints (("Goal" :in-theory (enable bv-array-read bv-array-write))))

;; ;drop?
;; (defthm endp-of-bv-array-write
;;   (equal (endp (bv-array-write esize len index val lst))
;;          (zp len))
;;   :hints (("Goal" :in-theory (enable update-nth2 bv-array-write))))

;rename to end in -of-bv-array-write
(defthmd nth-of-bv-array-write-becomes-bv-array-read
  (implies (and (< n len)
                (natp n)
                (natp len))
           (equal (nth n (bv-array-write esize len index val data))
                  (bv-array-read esize len n (bv-array-write esize len index val data))))
  :hints (("Goal" :in-theory (enable BV-ARRAY-READ update-nth2 bv-array-write ceiling-of-lg))))

(theory-invariant (incompatible (:definition bv-array-read) (:rewrite nth-of-bv-array-write-becomes-bv-array-read)))

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
                           (; GETBIT-OF-NTH-BECOMES-BV-ARRAY-READ BVCHOP-OF-NTH-BECOMES-BV-ARRAY-READ
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
  :hints (("Goal" :use bitxor-of-bv-array-read-and-bv-array-read-constant-arrays
           :in-theory (disable bitxor-of-bv-array-read-and-bv-array-read-constant-arrays))))

(defthm bvchop-list-of-update-nth2
  (implies (and (< key len)
                ;(<= len (+ 1 (len lst)))
                (<= len (len lst)) ;new
                (integerp len)
                (natp key))
           (equal (bvchop-list size (update-nth2 len key val lst))
                  (update-nth2 len key (bvchop size val) (bvchop-list size lst))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable update-nth2 update-nth
                                        bvchop-list))))

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
;;            :in-theory (e/d (bvchop-list-definition logext-list take )
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

(defthmd bv-array-read-of-bv-array-write-when-length-is-1
  (equal (bv-array-read size 1 index1 (bv-array-write size 1 index2 val data))
         (bvchop size val))
  :hints (("Goal" :in-theory (enable BV-ARRAY-WRITE
                                     BV-ARRAY-READ))))


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
  :hints (("Goal" :in-theory (enable bv-array-write bv-arrayp))))

;; (defthm bv-array-write-of-logext-list-better
;;   (implies (and (<= element-size size)
;;                 (natp size)
;;                 (natp element-size)
;;                 (natp len)
;;                 (natp key))
;;            (equal (bv-array-write element-size len key val (logext-list size lst))
;;                   (bv-array-write element-size len key val lst)))
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
;;   :HINTS
;;   (("Goal" :cases ((< INDEX (LEN LST)))
;;     :IN-THEORY (E/d (BVCHOP-WHEN-I-IS-NOT-AN-INTEGER
;;                        BV-ARRAY-READ) ()))))

;; Chops down the index if needed
(defthm bv-array-read-when-index-is-too-high
  (implies (and (syntaxp (and (quotep len)
                              (quotep index)))
                (not (unsigned-byte-p (ceiling-of-lg len) index))) ;prevents loops
           (equal (bv-array-read width len index arr)
                  (bv-array-read width len (bvchop (ceiling-of-lg len) index) arr)))
  :hints (("Goal" :in-theory (enable bv-array-read))))

;; Replaces myif with bv-array-if
(defthm bv-array-write-of-myif
  (implies (and (natp len)
                (natp width)
                (natp index))
           (equal (bv-array-write width len index val (myif test arr1 arr2))
                  (bv-array-write width len index val (bv-array-if width len test arr1 arr2))))
  :hints (("Goal" :in-theory (enable bv-array-if bv-array-write update-nth2))))

(defthm bv-arrayp-of-myif
  (equal (bv-arrayp element-width length (myif test val1 val2))
         (if test
             (bv-arrayp element-width length val1)
           (bv-arrayp element-width length val2))))

(defthmd bv-array-write-of-if-arg4 ; todo: gen to a "convert-to-bv" rule
  (implies (integerp element-size)
           (equal (bv-array-write element-size len index (if test val1 val2) data)
                  (bv-array-write element-size len index (bvif element-size test val1 val2) data)))
  :hints (("Goal" :in-theory (enable bvif))))

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

;; ;; Rules about treating bv-array-if as a list:
;; (defun bv-array-if-list-rules ()
;;   '(consp-of-bv-array-if
;;     car-of-bv-array-if
;;     cdr-of-bv-array-if
;;     nth-of-bv-array-if))

;; helps to resolve the size of the array, for translation to STP
(defthm bv-array-read-of-bvif-arg2
  (equal (bv-array-read element-size (bvif size2 test len1 len2) index data)
         (bvif element-size
               test
               (bv-array-read element-size (bvchop size2 len1) index data)
               (bv-array-read element-size (bvchop size2 len2) index data)))
  :hints (("Goal" :in-theory (enable bvif))))

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

;rename
(defthm array-reduction-0-1
  (implies (and (< 0 size)
                (integerp size))
           (equal (bv-array-read size 2 index '(0 1))
                  (getbit 0 index)))
  :hints (("Goal" :in-theory (enable bv-array-read nth-of-cons))))

;rename
(defthm array-reduction-1-0
  (implies (and (< 0 size)
                (integerp size))
           (equal (bv-array-read size 2 index '(1 0))
                  (bitnot (getbit 0 index))))
  :hints (("Goal" :in-theory (enable bitnot bv-array-read))))

(local
  (defthmd bv-array-read-when-all-same-helper
  (implies (and (equal data (repeat (len data) (car data))) ;expensive to check?
                (natp index)
                (< index len)
                (equal (len data) len)
                ;; (true-listp data)
                (all-unsigned-byte-p element-size data) ;drop?
                )
           (equal (bv-array-read element-size len index data)
                  (bv-array-read element-size len 0 data)
                  ;(bvchop element-size (car data))
                  ))
  :hints (("Goal"
           :in-theory (enable bv-array-read)))))

;; This could loop when INDEX is the constant 0, except that then the whole
;; bv-array-read should be evaluated because all the args would be constants.
;todo: use a binding hyp (and make an axe version with a binding hyp)
(defthmd bv-array-read-when-all-same
  (implies (and (syntaxp (and (quotep data)
                              (quotep len) ;these prevent loops
                              (quotep element-size)))
                ;; should be evaluated:
                (all-equal$ (bv-array-read element-size len 0 data) data) ;old way (involves consing): (equal data (repeat (len data) (car data)))
                (or (and (natp index)
                         (< index len))
                    ;; the the array is all zeros, we don't need to show that the index is good:
                    (equal 0 (bv-array-read element-size len 0 data)))
                (equal (len data) len) ; gets computed
                )
           (equal (bv-array-read element-size len index data)
                  ;; this should be ground and thus should be evaluated,
                  ;; so this rule should not loop:
                  (bv-array-read element-size len 0 data)))
  :hints (("Goal" :use (:instance bv-array-read-when-all-same-helper (data (true-list-fix data)))
           :in-theory (e/d (;all-equal$-when-true-listp
                            BV-ARRAY-READ)
                           (bv-array-read-when-all-same-helper ;car-becomes-nth-of-0
                            )))))

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

;see <-of-bv-and-constant
;todo: gen
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
                           (BV-ARRAY-READ-WHEN-ALL-SAME)))))

;rename
(defthmd bv-array-write-when-data-isnt-an-all-unsigned-byte-p
  (implies (and (syntaxp (and (quotep data)
                              (quotep esize)))
                (not (all-unsigned-byte-p esize data)) ; gets evaluated
                (equal (len data) len)
                (< INDEX (LEN DATA))
                (natp index)
                (true-listp data)
                (natp esize))
           (equal (bv-array-write esize len index val data)
                  (bv-array-write esize len index val (bvchop-list esize data))))
  :hints
  (("Goal"
    :cases ((<= (len data) (bvchop isize index)))
    :in-theory (enable  bvchop-when-i-is-not-an-integer
                       BV-ARRAY-WRITE
                       UPDATE-NTH2))))

;disable?
;rename
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
           :in-theory (enable
                       bv-array-write
                       bv-array-read
                       nth-when-<=-len
                       natp))))

;; the lhs should not arise when abstractions are being respected
(defthm BV-ARRAY-READ-of-cdr
  (implies (and (natp i)
;                (natp size)
                (equal len (+ -1 (LEN ARR)))
                (< i len))
           (EQUAL (BV-ARRAY-READ SIZE len I (CDR ARR))
                  (BV-ARRAY-READ SIZE (+ 1 len) (+ 1 I) ARR)))
  :hints (("Goal" :in-theory (e/d (bv-array-read ;ceiling-of-lg BVCHOP-OF-SUM-CASES
                                   )
                                  (BVCHOP-IDENTITY)))))

;; the lhs should not arise when abstractions are being respected
(defthm bv-array-read-of-nthcdr
  (implies (and (natp i)
                (< i (len src)))
           (equal (BV-ARRAY-READ 8 (LEN (NTHCDR I SRC)) 0 (NTHCDR I SRC))
                  (BV-ARRAY-READ 8 (LEN src) i src)))
  :hints (("Goal" :in-theory (enable BV-ARRAY-READ))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Make an empty array containing LEN zeros.  Element-size is included so you
;; can tell from the call what the type of the elements is.
(defun empty-bv-array (element-size len)
  (declare (ignore element-size))
  (repeat len 0))
