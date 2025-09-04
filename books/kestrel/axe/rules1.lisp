; Mixed rules 1
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

;; These are mostly about lists and arrays of BVs

;;  This file was called axerulescore.lisp.

;;(include-book "list-rules")
(include-book "kestrel/bv-lists/negated-elems-listp" :dir :system)
(include-book "kestrel/bv/unsigned-byte-p" :dir :system)
(include-book "kestrel/bv/bvcat" :dir :system)
(include-book "kestrel/bv/repeatbit" :dir :system)
(include-book "kestrel/bv/bvplus" :dir :system)
(include-book "kestrel/bv/rules" :dir :system) ; why?
;(include-book "kestrel/bv-lists/bvnth" :dir :system) ; todo: split out
(include-book "kestrel/bv-lists/bv-array-read-rules" :dir :system) ;drop?
(include-book "kestrel/bv-lists/bv-arrays" :dir :system) ; for bv-array-read-of-bvchop-list?
(include-book "kestrel/bv-lists/bv-array-clear" :dir :system)
(include-book "kestrel/bv-lists/bv-array-clear-range" :dir :system)
;(include-book "kestrel/typed-lists-light/integer-lists" :dir :system) ;for ALL-INTEGERP-WHEN-ALL-NATP
(include-book "kestrel/bv-lists/getbit-list" :dir :system)
(include-book "kestrel/lists-light/update-subrange" :dir :system)
(include-book "kestrel/lists-light/update-subrange2" :dir :system)
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/library-wrappers/arithmetic-inequalities" :dir :system)) ;todo, not trivial
(local (include-book "kestrel/bv-lists/all-unsigned-byte-p2" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt2" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/less-than" :dir :system))
(local (include-book "kestrel/arithmetic-light/integer-length" :dir :system))
(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))
(local (include-book "kestrel/lists-light/cons" :dir :system))
(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/lists-light/update-nth" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/firstn" :dir :system))
(local (include-book "kestrel/lists-light/cdr" :dir :system))

(local
 (defthmd even-when-power-of-2-and-at-least-2
   (implies (and (<= 2 n)
                 (power-of-2p n))
            (integerp (* 1/2 n)))
   :hints (("Goal" :in-theory (e/d (power-of-2p natp) (;exponents-add
                                                       ))))))

(local
 ;;gen
 (defthm +-of-half
   (equal (+ x (- (* 1/2 x)))
          (* 1/2 x))))

;; ;make local?
;; (defthmd true-listp-of-cdr-when-consp
;;   (implies (consp x)
;;            (equal (true-listp (cdr x))
;;                   (true-listp x))))

;move
;; (defthm equal-of-true-listp-when-equal-of-cdr
;;   (implies (and (equal (cdr lst) (cdr rhs))
;;                 (< 0 (len lst))
;;                 (< 0 (len rhs)))
;;            (equal (equal (true-listp rhs) (true-listp lst))
;;                   t))
;;   :hints (("Goal" :induct t
;;            :in-theory (enable true-listp))))

;(in-theory (disable TRUE-LISTP)) ; todo

;TTODO: Move these rules to the appropriate libraries!
;TODO: Handle the things with -dag in the name

;(local (in-theory (enable BVCHOP-WHEN-I-IS-NOT-AN-INTEGER)))

;(local (in-theory (disable NATP-WHEN-UNSIGNED-BYTE-P-SIZE-ARG)))

;(local (in-theory (disable LIST::FIX-OF-NTHCDR))) ;loops with NTHCDR-OF-TRUE-LIST-FIX !

;think about how to say this...
;; (defthm if-rule4
;;   (iff (if x x t) ;helps with ors?
;;          x)
;;   :rule-classes nil)

;; ;gets rid of extra bits in the bvcat indices - without this, we may have had big problems...
;; ;bozo gen?
;; (defthm bvnth-of-bvcat-8-case
;;   (implies (and (< 8 (+ n lowsize))
;;                 (natp lowsize)
;;                 (natp n)
;; ;                (natp esize)
;; ;                (equal 8 esize) ;bozo
;;                 )
;;            (equal (bvnth esize 8 (bvcat n highval lowsize lowval) data)
;;                   (if (<= 8 lowsize)
;;                       (bvnth esize 8 lowval data)
;;                     (bvnth esize 8 (bvcat (- 8 lowsize) highval lowsize lowval) data))))
;;   :hints (("Goal" :in-theory (enable bvnth))))

;; ;bozo gen this series
;; (defthm slice-7-0-bvnth
;;   (equal (slice 7 0 (bvnth 8 8 n data))
;;          (bvnth 8 8 n data)))

;; (defthm slice-15-8-bvnth
;;   (equal (slice 15 8 (bvnth 8 8 n data))
;;          0)
;;   :hints (("Goal" :in-theory (enable SLICE-TOO-HIGH-IS-0))))

;; (defthm slice-23-16-bvnth
;;   (equal (slice 23 16 (bvnth 8 8 n data))
;;          0)
;;   :hints (("Goal" :in-theory (enable SLICE-TOO-HIGH-IS-0))))

;; (defthm slice-31-24-bvnth
;;   (equal (slice 31 24 (bvnth 8 8 n data))
;;          0)
;;   :hints (("Goal" :in-theory (enable SLICE-TOO-HIGH-IS-0))))

;(in-theory (disable BVCAT-BVXOR-NEIGHBORS-HACK4)) ;loops!

;; (defthm slice-of-bvcat-hack-gen-better-case-1-eric
;;   (implies (and (> lowsize highbit)
;;                 (integerp lowsize)
;;                 (natp highsize)
;;                 (natp lowbit)
;;                 (natp highbit)
;;                 )
;;            (equal (slice highbit lowbit (bvcat highsize x lowsize y))
;;                   (slice highbit lowbit y))))

;; (skip -proofs
;;  (DEFTHM SLICE-OF-BVCAT-HACK-GEN-BETTER-case-2-eric
;;   (IMPLIES (AND (<= LOWSIZE HIGHBIT)
;;                 (< LOWBIT LOWSIZE)
;;                 ;(NATP LOWSIZE)
;;                 ;(NATP HIGHSIZE)
;;                 ;(NATP LOWBIT)
;;                 ;(NATP HIGHBIT)
;;                 )
;;            (EQUAL
;;             (SLICE HIGHBIT
;;                    LOWBIT (bvcat HIGHSIZE X LOWSIZE Y))
;;             (ULOGAPP (- LOWSIZE LOWBIT)
;;                      (SLICE (+ -1 LOWSIZE) LOWBIT Y)
;;                      (MIN HIGHSIZE (+ HIGHBIT (- LOWSIZE) 1))
;;                      (SLICE (MIN (- HIGHBIT LOWSIZE)
;;                                  (+ -1 HIGHSIZE))
;;                             0 X))))))

;; (skip -proofs
;;  (DEFTHM SLICE-OF-BVCAT-HACK-GEN-BETTER-case-3-eric
;;    (IMPLIES (AND (<= LOWSIZE HIGHBIT)
;;                  (<= LOWSIZE LOWBIT)
;; ;(NATP LOWSIZE)
;; ;(NATP HIGHSIZE)
;; ;(NATP LOWBIT)
;; ;(NATP HIGHBIT)
;;                  )
;;             (EQUAL
;;              (SLICE HIGHBIT
;;                     LOWBIT (bvcat HIGHSIZE X LOWSIZE Y))
;;              (SLICE (- HIGHBIT LOWSIZE)
;;                     (- LOWBIT LOWSIZE)
;;                     (BVCHOP HIGHSIZE X))))))


;; ;bozo simplify rhs? ;looped b/c rhs isn't simplified
;; (defthm bvcat-of-bvcat-trim-low-arg
;;   (implies (and (< size1 (+ highsize lowsize))
;;                 (natp size1)
;;                 (natp size2)
;; ;                (integerp x)
;;                 )
;;            (equal (bvcat size2 x size1 (bvcat highsize highval lowsize lowval))
;;                   (bvcat size2 x size1 (bvchop size1 (bvcat highsize highval lowsize lowval)))
;;                   ))
;;   :hints (("Goal"
;;            :use (:instance BVMULT-OF-BVCHOP-arg3
;;                            (size size)
;;                            (x (bvcat highsize highval lowsize lowval))
;;                            (y x))
;;            :in-theory (e/d ( ;bvmult
;;                             ) (  BVMULT-OF-BVCHOP-arg3)))))

;; (defthm bvmult-8-27-blast
;;   (equal (bvmult 8 27 (getbit n x))
;;          (BVCAT 1 (GETBIT N X)
;;                 4
;;                 (BVCAT 1 (GETBIT N X)
;;                        3 (BVCAT 1 (GETBIT N X) 1 (GETBIT N X)))))
;;   :hints (("Goal" :in-theory (e/d (BLAST-BVMULT-INTO-BVPLUS BLAST-BVPLUS) (BVCAT-EQUAL-REWRITE)))))

;; (defthm bvmult-8-27-blast-hack
;;   (equal (bvmult 8 27 (bitxor x y))
;;          (BVCAT 1 (bitxor x y)
;;                 4
;;                 (BVCAT 1 (bitxor x y)
;;                        3 (BVCAT 1 (bitxor x y) 1 (bitxor x y)))))
;;   :hints (("Goal" :in-theory (e/d (BLAST-BVMULT-INTO-BVPLUS BLAST-BVPLUS) (BVCAT-EQUAL-REWRITE)))))


;; ;drop?
;; (defthmd bvplus-trim-constant-arg1
;;   (implies (and (syntaxp (quotep x))
;;                 (syntaxp (quotep size))
;;                 (not (unsigned-byte-p size x)) ;intended to only apply to constants
;; ;                (integerp x)
;;  ;               (integerp y)
;;                 (natp size))
;;            (equal (bvplus size x y)
;;                   (bvplus size (bvchop size x) y)))
;;   :hints (("Goal" :in-theory (e/d (bvplus) ()))))

;; (defthmd bvminus-solve-for-dag2
;;   (implies (and (syntaxp (quotep k))
;;                 (syntaxp (quotep k2))
;;                 (syntaxp (quotep n))
;;                 (natp n)
;;                 (integerp x)
;;                 (integerp k)
;;                 (integerp k2))
;;            (equal (equal (bvminus n k2 x) k)
;;                   (and (unsigned-byte-p n k) ;is this isn't the case, the equality is nil
;;                        (equal (bvminus n k2 k) (bvchop n x)))))
;;   :hints (("Goal" :use (:instance bvminus-solve)
;;            :in-theory (disable bvminus-solve))))

;; ;bozo gen
;; ;bozo - needed because we equate an 8-bit signal with a 9-bit signal (this sort of thing wouldn't be needed if we bit blasted...)
;; ;would be better to rewrite the equality? hmmm. i dunno.
;; (defthm bvxor-8-9-tighten
;;   (implies (and (unsigned-byte-p 8 x)
;;                 (unsigned-byte-p 8 y))
;;            (equal (bvxor 9 x y)
;;                   (bvxor 8 x y)))
;;   :hints (("Goal" :in-theory (e/d (bvxor) (logxor-bvchop-bvchop ;hide-bvxor
;;                                              )))))

;dups among rules??: :pl  (unsigned-byte-p 8 (bvcat 8 x 1 y))

;; (defthmd nth-of-slice-becomes-nth2
;;   (implies (and (natp high)
;;                 (natp low)
;;                 (<= low high))
;;            (equal (nth (slice high low index)  lst)
;;                   (nth2 (+ 1 high (- low)) (slice high low index) lst)))
;;   :hints (("Goal" :in-theory (enable nth2))))

;; (defthmd nth-of-bvchop-becomes-nth2
;;   (equal (nth (bvchop size index)  lst)
;;          (nth2 size (bvchop size index) lst))
;;   :hints (("Goal" :in-theory (enable nth2))))

;; (defthmd nth-of-bvxor-becomes-nth2
;;   (implies (and (natp size))
;;            (equal (nth (bvxor size x y)  lst)
;;                   (nth2 size (bvxor size x y) lst)))
;;   :hints (("Goal" :in-theory (enable nth2))))

;; (defthmd nth-of-bvcat-becomes-nth2
;;   (implies (and (natp highsize)
;;                 (natp lowsize)
;;                 (<= lowsize highsize))
;;            (equal (nth (bvcat highsize highval lowsize lowval)  lst)
;;                   (nth2 (+ highsize lowsize) (bvcat highsize highval lowsize lowval) lst)))
;;   :hints (("Goal" :in-theory (enable nth2))))

;; (defthmd nth2-becomes-bvnth-for-natps
;;   (implies (and (all-natp vals)
;;                 (natp indexsize)
;;                 (natp index)
;;                 (< index (len vals))
;;                 )
;;            (equal (nth2 indexsize index vals)
;;                   (bvnth (width-of-widest-int vals)
;;                          indexsize
;;                          index
;;                          vals)))
;;   :hints (("Goal"
;;            :cases ((<= (bvchop indexsize index) index))
;;            :in-theory (enable nth2 bvnth ;all-integerp-when-all-natp
;;                               ))))

;; (defthm nth2-becomes-bvnth-for-signed-byte-data
;;   (implies (and (all-signed-byte-p (+ 1 (width-of-widest-int vals)) vals)
;;                 (natp indexsize)
;;                 (natp index)
;;                 (< index (len vals))
;;                 )
;;            (equal (nth2 indexsize index vals)
;;                   (logext (+ 1 (width-of-widest-int vals))
;;                           (bvnth (+ 1 (width-of-widest-int vals))
;;                                  indexsize
;;                                  index
;;                                  vals))))
;;   :hints (("Goal" ;:cases ((natp index) (not (integerp index)))
;;            :in-theory (enable bvnth all-integerp-when-all-natp nth2
;;                               BVCHOP-WHEN-I-IS-NOT-AN-INTEGER
;;                                      ADD-BVCHOPS-TO-EQUALITY-OF-SBPS-4-ALT))))

;; (defthm getbit-of-bvnth-too-high
;;   (implies (and (<= size n)
;;                 (natp n)
;;                 (natp size))
;;            (equal (getbit n (bvnth size isize index vals))
;;                   0))
;;   :hints (("Goal" :in-theory (enable getbit-too-high))))

;; (DEFTHMd NTH2-BECOMES-BVNTH-8
;;   (IMPLIES (AND (all-unsigned-byte-p 8 vals)
;;                 ;;(ALL-NATP VALS)
;;                 (NATP INDEXSIZE)
;;                 (NATP INDEX)
;;                 (< INDEX (LEN VALS)))
;;            (EQUAL (NTH2 INDEXSIZE INDEX VALS)
;;                   (BVNTH 8 INDEXSIZE INDEX VALS)))
;;   :HINTS
;;   (("Goal"
;;     :CASES ((<= (BVCHOP INDEXSIZE INDEX) INDEX))
;;     :IN-THEORY (E/d (NTH2 BVNTH
;;                           ALL-INTEGERP-WHEN-ALL-NATP) ()))))

;Thu Mar  4 15:56:21 2010
;; (skip -proofs
;; (defthm logext-list-of-update-nth2
;;    (implies (and (< key len)
;;                  (natp len)
;;                  (natp key))
;;             (equal (logext-list size (update-nth2 len key val lst))
;;                    (update-nth2 len key (logext size val)
;;                                 (logext-list size lst))))
;;    :hints
;;    (("Goal" :do-not '(generalize eliminate-destructors)
;;      :in-theory (e/d (update-nth2 logext-list) (TAKE-OF-CDR-BECOMES-SUBRANGE
;;                                                 take-of-logext-list))))))

;; (defthmd update-nth2-becomes-bv-array-write32-signed-case
;;   (implies (and (all-signed-byte-p 32 lst)
;;                 (signed-byte-p 32 val)
;;                 (true-listp lst)
;;                 (NATP LEN)
;;                 (NATP KEY)
;;                 (< KEY LEN))
;;            (equal (update-nth2 len key val lst)
;;                   (logext-list 32 (bv-array-write 32 len key val lst))))
;;   :hints (("Goal" :in-theory (disable ;BVCHOP-LIST-WHEN-CONSP
;;                                       ))))

;(in-theory (disable BVCHOP-LIST-WHEN-CONSP))

;;(ALL-UNSIGNED-BYTE-P M (REPEAT N NIL))

;; (DEFTHMd NTH2-BECOMES-BVNTH-32
;;   (IMPLIES (AND (all-unsigned-byte-p 32 vals)
;;                 ;(ALL-NATP VALS)
;;                 (NATP INDEXSIZE)
;;                 (NATP INDEX)
;;                 (< INDEX (LEN VALS)))
;;            (EQUAL (NTH2 INDEXSIZE INDEX VALS)
;;                   (BVNTH 32 INDEXSIZE INDEX VALS)))
;;   :HINTS
;;   (("Goal"
;;     :CASES ((<= (BVCHOP INDEXSIZE INDEX) INDEX))
;;     :IN-THEORY (E/d (NTH2 BVNTH
;;                        ALL-INTEGERP-WHEN-ALL-NATP) ()))))

;; ;bbozo gross
;; (defthmd bvnth-tighten-32-8
;;   (implies (all-unsigned-byte-p 8 data)
;;            (equal (bvnth 32 index-size index data)
;;                   (bvnth 8 index-size index data)))
;;   :hints (("Goal" :cases ((< (BVCHOP INDEX-SIZE INDEX) (LEN DATA)))
;;            :in-theory (enable bvnth slice-too-high-is-0
;;                               ;;LIST::NTH-WITH-LARGE-INDEX
;;                               ))))

;BOZO classify these rules somehow (separate the ones for the symbolic simulation?)

;; (defthmd not-<-self2
;;   (implies (equal x y)
;;            (not (< x y))))

;; ;just a special case of a cancellation rule
;; (defthm <-of-+-of-1-same
;;   (< x (+ 1 x)))

;; ;just a special case of a cancellation rule
;; (defthm <-of-+-of-1-same-alt
;;   (not (< (+ 1 x) x)))

;; (defthm hack-arith-cancel
;;   (equal (< (+ a x) (+ b x))
;;          (< a b)))



;; ;drop? expensive?
;; (defthmd usbp8-implies-sbp32-2
;;   (implies (unsigned-byte-p 8 x)
;;            (signed-byte-p 32 x)))

;; ;fixme the same as append-of-cons?
;; (DEFTHM LIST::xAPPEND-OF-CONS-BETTER2
;; ;  (IMPLIES (SYNTAXP (NOT (AND (QUOTEP X) (QUOTEP A))))
;;            (EQUAL (APPEND (CONS A X) Y)
;;                   (CONS A (APPEND X Y)))
;;            ;)
;;   :HINTS
;;   (("Goal" :IN-THEORY (DISABLE LIST::EQUAL-APPEND-REDUCTION!))))

;; (DEFTHM UPDATE-NTH2-OF-CONS
;;   (EQUAL (UPDATE-NTH2 len N VAL (CONS A LST))
;;          (IF (ZP N)
;;              (CONS VAL LST)
;;              (CONS A (UPDATE-NTH (+ -1 N) VAL LST)))))

;bozo some dups above this?

;; ;TODO: do we still use bvnth?
;; ;move?
;; (defthm bvnth-becomes-bv-array-read
;;   (implies (and (natp index-size)
;;                 ;; (< index (expt 2 index-size))
;;                 ;; (natp index)
;;                 )
;;            (equal (bvnth element-size index-size index data)
;;                   (bv-array-read element-size (expt 2 index-size) (bvchop index-size index) data)))
;;   :hints (("Goal" :in-theory (enable bv-array-read bvnth ceiling-of-lg))))

;=== stuff to support array-reduction-when-top-bit-is-xored-in

;bozo may be slow?
;; (defthm bit-listp-implies-all-integerp
;;   (implies (all-unsigned-byte-p 1 vals)
;;            (all-integerp vals))
;;   :hints (("Goal" :in-theory (enable all-integerp))))


;; (defthm nth-of-bitnot-list
;;   (implies (and (natp n)
;;                 (< n (len lst)))
;;            (equal (nth n (bitnot-list lst))
;;                   (bitnot (nth n lst))))
;;   :hints
;;   (("Goal" :in-theory (e/d (nth bitnot-list) (nth-of-cdr)))))



;; (thm
;;  (implies (and (posp n) (natp x))
;;           (equal (lognot (bvchop n (lognot x)))
;;                  (bvchop n x)))
;;  :hints (("Goal" :in-theory (enable lognot))))

;; (thm
;;  (IMPLIES (AND (POSP N) (NATP X))
;;           (EQUAL (LOGIOR (- (EXPT 2 N)) (BVCHOP N X))
;;                  (BVCHOP N X)))
;;  :hints (("Goal" :in-theory (enable logior))))

;; (thm
;;  (implies (and (posp n)
;;                (natp x))
;;           (equal (logeqv (+ -1 (expt 2 n))
;;                          (bvchop n x))
;;                  (bvchop n x)))
;;  :hints (("Goal" :in-theory (e/d (logeqv logorc1 ;lognot-of-logior-back
;;                                           lognot-of-logand
;;                                          ) (
;;                                             lognot-of-logior)))))

;does trim apply to repeatbit?

;; (defthmd car-of-both-sides
;;   (implies (and (equal x y)
;;                 (equal (car x) w)
;;                 (equal (car y) z))
;;            (equal (equal w z)
;;                   t)))

;; (defthmd car-of-both-sides-alt
;;   (implies (and (equal y x)
;;                 (equal (car x) w)
;;                 (equal (car y) z))
;;            (equal (equal w z)
;;                   t)))

;newly disabled
;rename!
(local
  (defthmd gross-hack
    (IMPLIES (AND ;(UNSIGNED-BYTE-P ELEM-SIZE (NTH (EXPT 2 N) VALS))
               (EQUAL (BVNOT-LIST ELEM-SIZE (TAKE (EXPT 2 N) VALS))
                      (NTHCDR (EXPT 2 N) VALS))
               (NATP N)
               (EQUAL (LEN VALS) (* 2 (EXPT 2 N)))
               (TRUE-LISTP VALS)
               (NATP ELEM-SIZE))
             (EQUAL (BVCHOP ELEM-SIZE (NTH (EXPT 2 N) VALS))
                    (BVNOT ELEM-SIZE (NTH 0 VALS))))
    :hints (("Goal" :expand ((BVNOT-LIST ELEM-SIZE (TAKE (EXPT 2 N) VALS))
                             (NTHCDR (EXPT 2 N) VALS))
             :in-theory (disable NTHCDR-OF-CDR-COMBINE-STRONG NTHCDR-OF-CDR-COMBINE)
             ))))

(local
  (defthmd array-reduction-when-top-bit-is-xored-in-helper-helper
    (implies (and (equal (bvnot-list elem-size (firstn (expt 2 n) vals)) ;why subrange?
                         (subrange (expt 2 n) (+ -1 (expt 2 n) (expt 2 n)) vals))
                  (natp n)
                  (equal (len vals) (expt 2 (+ 1 n)))
                  (true-listp vals)
                  (natp elem-size)
                  )
             (equal (bv-array-read elem-size (expt 2 (+ 1 n)) (bvcat 1 x n y) vals)
                    (bvxor elem-size
                           (repeatbit elem-size (getbit 0 x))
                           (bv-array-read elem-size (expt 2 n) (bvchop n y) (firstn (expt 2 n) vals)))))
    :hints (("Goal"
             :cases ((equal 0 (getbit 0 x)))
             :use (:instance gross-hack)
             :in-theory (e/d (expt-of-+
                              bvplus ;-opener
                              nth-sum-when-nthcdr-known
                              bvcat-special-opener
                              bv-array-read ceiling-of-lg
                              ;; car-of-both-sides-alt
                              ;; car-of-both-sides
                              ;; bvchop-of-+-becomes-bvplus
                              ;; EXPONENTS-ADD-FOR-NONNEG-EXPONENTS
                              subrange)
                             (gross-hack
                              nth-of-cdr
                              NTH-OF-NTHCDR ;looped
                              REPEATBIT-OF-1-ARG2
                              NTHCDR-OF-CDR-COMBINE-STRONG NTHCDR-OF-CDR-COMBINE
                            ;NTH-OF-TAKE-GEN
                            ;NTH-OF-BVNOT-LIST
                            ;BV-ARRAY-READ-OF-TAKE
                            ;BV-ARRAY-READ-OF-BVCHOP
                            ;BV-ARRAY-READ-OF-BVCHOP-HELPER
                              ))))))

(local
  (defthm array-reduction-when-top-bit-is-xored-in-helper
    (implies (and (equal (bvnot-list elem-size (firstn (expt 2 n) vals))
                         (subrange (expt 2 n) (+ -1 (expt 2 (+ 1 n))) vals))
                  (natp n)
                  (equal (len vals) (expt 2 (+ 1 n)))
                  (natp elem-size)
                  )
             (equal (bv-array-read elem-size (expt 2 (+ 1 n)) index vals)
                    (bvxor elem-size (repeatbit elem-size (getbit n index))
                           (bv-array-read elem-size (expt 2 n) (bvchop n index) (firstn (expt 2 n) vals)))))
    :hints (("Goal" :in-theory (enable expt-of-+ subrange)
             :use (:instance array-reduction-when-top-bit-is-xored-in-helper-helper
                             (x (getbit n index))
                             (y (bvchop n index))
                             (vals (true-list-fix vals)))))))

;we could do the (equal (bvnot-list ..) ..) check without consing:
;in general, if we have the equality of 2 lists built up by consing, we can build them up in parallel and stop as soon as one difference is found
(defthm array-reduction-when-top-bit-is-xored-in
  (implies (and (syntaxp (quotep array)) ;require len and elem-size to be quoteps too?
                (power-of-2p len)
                (<= 2 len)
                (negated-elems-listp elem-size (nthcdr (/ len 2) array) array) ;this should fail fast..
                (equal len (len array)) ;new
                (true-listp array) ;new
                ;this is still slow:
;;                 (equal (bvnot-list elem-size (take (/ len 2) array))
;;                        (nthcdr (/ len 2) array) ;;slow: (subrange (/ len 2) (+ -1 len) array) ;ffixme this could just be an nthcdr?
;;                        )
                (natp elem-size))
           (equal (bv-array-read elem-size len index array)
                  (bvxor elem-size
                         (repeatbit elem-size (getbit (+ -1 (lg len)) index))
                         (bv-array-read elem-size
                                        (/ len 2)
                                        (bvchop (+ -1 (lg len)) index)
                                        (firstn (/ len 2) array)))))
  :hints (("Goal"
           :in-theory (e/d (expt-2-of-integer-length-when-power-2p ;power-of-2p
                            expt-of-+
                            ceiling-of-lg
                            natp even-when-power-of-2-and-at-least-2 lg
                            SUBRANGE ;prove an nthcdr=subrange rule
                            )
                           (array-reduction-when-top-bit-is-xored-in-helper ;TAKE-WHEN-<-OF-LEN

                                                                            ;NTHCDR-OF-TAKE-BECOMES-SUBRANGE
                                                                            ))
           :use (:instance array-reduction-when-top-bit-is-xored-in-helper
                           (vals (bvchop-list elem-size (take len (true-list-fix array))))
                           (n (+ -2 (integer-length len)))))))

(local
 (defthm bvchop-of-one-more-of-+-of-expt2
   (implies (natp n)
            (equal (BVCHOP (+ 1 N) (+ (EXPT 2 N) (BVCHOP N Y)))
                   (+ (expt 2 n) (bvchop n y))))
   :hints (("Goal" :in-theory (enable UNSIGNED-BYTE-P expt-of-+)))))

(local
  (defthm array-reduction-when-top-bit-is-irrelevant-helper
    (implies (and ;(integerp y)
               ;;(<= 0 y)
               (natp n)
               (equal (len vals) (expt 2 (+ 1 n)))
               (true-listp vals)
               (all-unsigned-byte-p 1 vals)
               (equal (firstn (expt 2 n) vals)
                      (subrange (expt 2 n) (+ -1 (expt 2 n) (expt 2 n)) vals))
               )
             (equal (bv-array-read 1 (expt 2 (+ 1 n)) (bvcat 1 x n y) vals)
                    (bv-array-read 1 (expt 2 n) (bvchop n y) (firstn (expt 2 n) vals))))
    :hints (("Goal"
             :cases ((equal 0 (getbit 0 x)))
             :in-theory (e/d (nth-sum-when-nthcdr-known bvcat-special-opener bv-array-read ceiling-of-lg subrange)
                             (NTH-OF-NTHCDR
                              BV-ARRAY-READ-OF-BVCHOP-HELPER
                              BV-ARRAY-READ-OF-BVCHOP
                              BV-ARRAY-READ-OF-TAKE))))))

;todo: gen to more than 1 bit
(defthm array-reduction-when-top-bit-is-irrelevant
  (implies (and (syntaxp (quotep vals)) ;Sat Mar 20 08:56:01 2010
                 (equal (firstn (/ len 2) vals) ;fixme slow?
                        (nthcdr (/ len 2) vals) ;slower: (subrange (/ len 2) (+ -1 len) vals)
                        )
                (equal mm (+ -2 (integer-length len)))
                (<= 2 (integer-length (len vals)))               ;drop?
                (equal len (expt 2 (+ -1 (integer-length len)))) ;len is a power of 2
                (equal (len vals) len)
                (true-listp vals)
                (all-unsigned-byte-p 1 vals)
                )
           (equal (bv-array-read 1 len (bvcat 1 x mm y) vals) ;gen the bvcat?
                  (bv-array-read 1 (/ len 2) (bvchop (+ -2 (integer-length len)) y) (firstn (/ len 2) vals))))
  :hints (("Goal"
           :in-theory (e/d (expt-of-+ ;expt-move-hack
                            ;bvplus-opener
                            subrange
                            )
                           ( ;EQUAL-*-/-1
                            array-reduction-when-top-bit-is-irrelevant-helper
                            firstn bv-array-read))
           :use (:instance array-reduction-when-top-bit-is-irrelevant-helper
                           (n (+ -2 (integer-length len)))))))

;; (thm
;;  (IMPLIES (< INDEX 0)
;;           (EQUAL (GETBIT 0 INDEX)
;;                  0))
;;  :hints (("Goal" :in-theory (e/d (getbit) ( )))))

;; ;yuck?
;; (defthmd myif-of-constant-lists
;;   (implies (and (syntaxp (quotep l1))
;;                 (syntaxp (quotep l2))
;;                 (consp l1)
;;                 (consp l2)
;;                 )
;;            (equal (myif test l1 l2)
;;                   (cons (myif test (car l1) (car l2))
;;                         (myif test (cdr l1) (cdr l2)))))
;;   :hints (("Goal" :in-theory (enable myif))))

;; (defthm myif-of-logext-list-arg1
;;   (implies (and (all-signed-byte-p n y)
;;                 (true-listp y)
;;                 (integerp n)
;;                 (< 0 n))
;;            (equal (myif test (logext-list n x) y)
;;                   (logext-list n (myif test x y))))
;;   :hints (("Goal" :in-theory (enable myif))))

;; (defthm myif-of-logext-list-arg2
;;   (implies (and (all-signed-byte-p n y)
;;                 (true-listp y)
;;                 (integerp n)
;;                 (< 0 n))
;;            (equal (myif test y (logext-list n x))
;;                   (logext-list n (myif test y x))))
;;   :hints (("Goal" :in-theory (enable myif))))


;keep but move
;; (defthm all-signed-byte-p-of-logext-list
;;   (implies (and (integerp size)
;;                 (< 0 size))
;;            (equal (all-signed-byte-p size (logext-list size lst))
;;                   t))
;;   :hints (("Goal" :in-theory (enable logext-list all-signed-byte-p))))

;yuck?
;; (defthm all-signed-byte-p-of-bv-array-write
;;   (implies (and (unsigned-byte-p (+ -1 n) (bvchop n val))
;;                 (all-unsigned-byte-p (+ -1 n) (bvchop-list n lst))
;;                 (natp index)
;;                 (true-listp lst)
;;                 (< index (len lst))
;;                 (equal len (len lst))
;;                 (natp n)
;;                 (< 0 n)
;;                 )
;;            (equal (all-signed-byte-p n (BV-ARRAY-WRITE n len index val lst))
;;                   t))
;;   :hints (("Goal" :in-theory (e/d (UPDATE-NTH2 BV-ARRAY-WRITE)
;;                                   (REWRITE-UNSIGNED-BYTE-P-WHEN-TERM-SIZE-IS-LARGER)))))

;; (thm
;;  (IMPLIES (AND (< X K)
;;                (< Y K)
;;                (NATP K)
;;                (NATP X)
;;                (NATP Y))
;;           (<= (- K) (LOGEQV X Y)))
;;  :hints (("Goal" :in-theory (enable logeqv LOGORC1 logior))))

;; (thm
;;  (IMPLIES (AND (< x K)
;;                (< y K)
;;                (NATP K)
;;                (NATP x)
;;                (NATP y))
;;           (< (LOGXOR x y) K))
;;  :hints (("Goal" :in-theory (enable logxor))))


;; (defun triple-floor-by-2-induct (i j n)
;;   (if (zip i)
;;       (list i j n)
;;       (if (= i -1)
;;           0
;;           (if (zip j)
;;               0
;;               (if (= j -1)
;;                   0
;;                   (+ 1 (triple-floor-by-2-induct (floor i 2) (floor j 2) (floor n 2))))))))


;bozo gen
;fixme problems due to nfix around bv-array-read index
(defthmd bv-array-read-of-logext-64-32
  (implies (and ; (unsigned-byte-p 32 x)
;               (<= 0 (logext 32 x))
            (integerp x)
            (integerp m)
            (<= 6 m)
            )
           (equal (bv-array-read n 64 (logext m x) vals)
                  (bv-array-read n 64 (bvchop 6 x) vals)))
  :hints (("Goal" :in-theory (enable bv-array-read BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))))

;move
;; (defthm getbit-list-of-logext-list
;;   (implies (and (< n size)
;;                 (natp size)
;;                 (natp n))
;;            (equal (getbit-list n (logext-list size lst))
;;                   (getbit-list n lst)))
;;   :hints (("Goal" :in-theory (enable getbit-list logext-list))))

;use a trim rule!
(defthmd bv-array-write-of-bvcat-reduce
  (implies (and (<= element-size lowsize) ; so highval is irrelevant
                (natp element-size)
                (natp highsize)
                (natp lowsize)
                (equal len (len lst))
                (< index len)
                (natp index))
           (equal (bv-array-write element-size len index (bvcat highsize highval lowsize lowval) lst)
                  (bv-array-write element-size len index lowval lst)))
  :hints (("Goal" :in-theory (enable update-nth2 bv-array-write))))

(defthm bv-array-read-of-getbit-list
  (implies (and (< n esize) ;bozo
                (equal len (len data))
                ;(< 1 esize)
                (< i len)
                (natp i)
                (natp n)
                (natp esize)
                )
           (equal (bv-array-read esize len i (getbit-list n data))
                  (getbit n (bv-array-read esize len i data))))
  :hints
  (("Goal" :do-not '(generalize eliminate-destructors)
    :cases ((<= ESIZE N))
    :in-theory (e/d (bv-array-read ;bvnth
                     GETBIT-WHEN-VAL-IS-NOT-AN-INTEGER ;NTH-WHEN-N-IS-ZP
                                   )
                    (nth-of-cdr CAR-BECOMES-NTH-OF-0)))))

;bozo now delete some rules with constants as arg2 - same thing for bvmult and other binary functions?

;(local (in-theory (enable myif)))

;; ;drop?   breaks the bv-array abstraction
;; (defthmd bytes-to-bits-of-bv-array-write
;;   (implies (and (equal len (len lst))
;;                 (< n len)
;;                 (true-listp lst)
;;                 (natp n)
;;                 )
;;            (equal (bytes-to-bits (bv-array-write 8 len n val lst))
;;                   (append (bytes-to-bits (take n lst))
;;                           (list (getbit 7 val)
;;                                 (getbit 6 val)
;;                                 (getbit 5 val)
;;                                 (getbit 4 val)
;;                                 (getbit 3 val)
;;                                 (getbit 2 val)
;;                                 (getbit 1 val)
;;                                 (getbit 0 val))
;;                           (bytes-to-bits (nthcdr (+ 1 n) lst))
;;                           )))
;;   :hints (("Goal"
;;            :expand (BYTES-TO-BITS (UPDATE-NTH 0 VAL (NTHCDR N LST)))
;;            :in-theory (enable bytes-to-bits byte-to-bits update-nth2 bv-array-write ceiling-of-lg equal-of-append CDR-OF-NTHCDR))))

;; (defun dag-nodes-with-fn (fn dag)
;; ;  (declare (xargs :guard (alistp dag)))
;;   (if (endp dag)
;;       nil
;;     (let* ((entry (car dag))
;;            (expr (cdr entry)))
;;       (if (and (consp expr)
;;                (equal fn (car expr)))
;;           (prog2$ (cw "~x0~%" entry)
;;                   (dag-nodes-with-fn fn (cdr dag)))
;;         (dag-nodes-with-fn fn (cdr dag))))))

;bozo clean this up - drop the bvchops or the usb hyp
;bozo gen
(defthm bv-array-read-of-upddate-subrange-128
  (implies (and (<= start (bvchop 7 n))
                (<= (bvchop 7 n) end)
                (unsigned-byte-p 7 n) ;drop
;                (<= start end)
                (natp end)
                (natp start)
                (natp n))
           (equal (BV-ARRAY-READ esize '128 n (UPDATE-SUBRANGE start end vals lst))
                  (BV-ARRAY-READ esize (+ 1 end (- start)) (+ N (- START)) vals)))
  :hints (("Goal" :in-theory (e/d (bv-array-read unsigned-byte-p-of-integer-length-gen ceiling-of-lg)
                                  (unsigned-byte-p-of-+-of-minus-alt
                                   unsigned-byte-p-of-+-of-minus)))))

;; (thm
;;  (equal (repeatbit 1 bit)
;;         (getbit 0 bit))
;;  :hints (("Goal" :in-theory (enable repeatbit))))

(defthm getbit-list-of-bv-array-write
  (implies (and (< n esize) ;other case (all zeros)?
                (equal len (len lst)) ;drop?
                (< key len) ;drop?
                (natp n)
                (natp esize)
                (natp key)
                (natp len))
           (equal (getbit-list n (bv-array-write esize len key val lst))
                  ;drop the fix?
                  (bv-array-write 1 len key (getbit n val) (getbit-list n (true-list-fix lst)))))
  :hints (("Goal" :in-theory (enable UPDATE-NTH2 bv-array-write))))

;; ;not true for negative vals!
;; (defthm nth-of-bvcat-becomes-bvnth-for-natps
;;   (implies (and (all-natp vals)
;;                 (natp HIGHSIZE)
;;                 (natp lowsize)
;;                 (< (bvcat highsize highval lowsize lowval) (len vals))
;;                 )
;;            (equal (nth (bvcat highsize highval lowsize lowval) vals)
;;                   (bvnth (width-of-widest-int vals)
;;                          (+ highsize lowsize)
;;                          (bvcat highsize highval lowsize lowval)
;;                          vals)))
;;   :hints (("Goal" :in-theory (enable bvnth all-integerp-when-all-natp))))

;; (defthm nth-of-bvcat-becomes-bvnth-for-signed-byte-data
;;   (implies (and (all-signed-byte-p (+ 1 (width-of-widest-int vals)) vals)
;;                 (natp highsize)
;;                 (natp lowsize)
;;                 (< (bvcat highsize highval lowsize lowval) (len vals))
;;                 )
;;            (equal (nth (bvcat highsize highval lowsize lowval) vals)
;;                   (logext (+ 1 (width-of-widest-int vals))
;;                           (bvnth (+ 1 (width-of-widest-int vals))
;;                                  (+ highsize lowsize)
;;                                  (bvcat highsize highval lowsize lowval)
;;                                  vals))))
;;   :hints (("Goal" :in-theory (enable bvnth all-integerp-when-all-natp
;;                                      ADD-BVCHOPS-TO-EQUALITY-OF-SBPS-4-ALT))))

;needed for 2d arrays - BOZO gen!
(defthm split-nth-access-hack
  (equal (nth (bvcat 1 a 1 b) vals)
         (if (equal 0 (getbit 0 a))
             (if (equal 0 (getbit 0 b))
                 (nth 0 vals)
               (nth 1 vals))
           (if (equal 0 (getbit 0 b))
               (nth 2 vals)
             (nth 3 vals))))
  :hints (("Goal"
           :cases ((and (equal 1 (getbit 0 a)) (equal 1 (getbit 0 b)))
                   (and (not (equal 1 (getbit 0 a))) (equal 1 (getbit 0 b)))
                   (and (equal 1 (getbit 0 a)) (not (equal 1 (getbit 0 b)))))
           :in-theory (disable ;GETBIT-WHEN-NOT-0
                       ;;GETBIT-WHEN-NOT-1
                               ))))

(defthmd nth-of-if-arg2
  (equal (nth n (if test a b))
         (if test (nth n a) (nth n b))))

;; (defthm myif-of-logext-list-and-logext-list
;;   (equal (myif test (logext-list n x) (logext-list n y))
;;          (logext-list n (myif test x y)))
;;   :hints (("Goal" :in-theory (enable myif))))

;; (defund MAX-INTEGER-LENGTH (lst)
;;   (if (endp lst)
;;       0 ;hope this is okay
;;     (max (integer-length (car lst))
;;          (MAX-INTEGER-LENGTH (cdr lst)))))

;; (defthm max-integer-length-bound
;;   (implies (and (< n (len lst))
;;                 (natp n))
;;            (<= (INTEGER-LENGTH (NTH n Lst))
;;                (MAX-INTEGER-LENGTH Lst)))
;;   :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;            :in-theory (e/d (MAX-INTEGER-LENGTH nth) (nth-of-cdr)))))

;; ;fixme
;; (skip -proofs
;; (defthmd myif-of-constant-lists-array-version
;;    (implies (and (syntaxp (quotep l1))
;;                  (syntaxp (quotep l2))
;;                  (equal (len l1) (len l2))
;;                  (consp l1) ;drop?
;;                  (consp l2) ;drop?
;;                  (all-natp l1)
;;                  (all-natp l2)
;;                  )
;;             (equal (myif test l1 l2)
;;                    (bv-array-write (max (MAX-INTEGER-LENGTH l1) (MAX-INTEGER-LENGTH l2))
;;                                    (len l1)
;;                                    0
;;                                    (myif test (car l1) (car l2))
;;                                    (myif test (cdr l1) (cdr l2)))))
;;    :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;             :in-theory (enable myif UPDATE-NTH2 LIST::UPDATE-NTH-EQUAL-REWRITE)))))

;; ;bozo prove me
;; (skip -proofs
;;  (defthm s-shlalt-rewrite
;;    (implies (and (integerp x)
;;                  (integerp n)
;;                  (<= 0 n))
;;             (equal (jvm::s-shlalt x n)
;;                    (logext 32 (bvcat (+ 32 (- n)) x n 0))))
;;    :hints (("Goal"
;;             :cases ((<= n 32))
;;             :in-theory (e/d (bvcat ;logapp
;;                              slice
;;                              BVCHOP-OF-LOGAPP-BIGGER
;;                              LOGTAIL-BVCHOP
;;                              logtail
;;                              ) (bvcat-recombine
;;                              BVCHOP-OF-LOGTAIL
;;                              LOGTAIL-BECOMES-SLICE-BIND-FREE
;;                              LOGTAIL-OF-BVCHOP-BECOMES-SLICE
;;                              SLICE-BECOMES-BVCHOP))))))

;these two from des:

;; (DEFTHMd MYIF-OF-LOGEXT-LIST-ARG2-constant-version
;;   (IMPLIES (AND (syntaxp (quotep y))
;;                 (syntaxp (quotep n))
;;                 (ALL-SIGNED-BYTE-P N Y)
;;                 (TRUE-LISTP Y)
;;                 (INTEGERP N)
;;                 (< 0 N))
;;            (EQUAL (MYIF TEST Y (LOGEXT-LIST N X))
;;                   (LOGEXT-LIST N (MYIF TEST Y X))))
;;   :HINTS (("Goal" :IN-THEORY (ENABLE MYIF))))

;; (DEFTHMd MYIF-OF-LOGEXT-LIST-ARG1-constant-version
;;   (IMPLIES (AND (syntaxp (quotep y))
;;                 (syntaxp (quotep n))
;;                 (ALL-SIGNED-BYTE-P N Y)
;;                 (TRUE-LISTP Y)
;;                 (INTEGERP N)
;;                 (< 0 N))
;;            (EQUAL (MYIF TEST (LOGEXT-LIST N X) Y)
;;                   (LOGEXT-LIST N (MYIF TEST X Y))))
;;   :HINTS (("Goal" :IN-THEORY (ENABLE MYIF))))


;; (DEFTHMd NTH-OF-BVCAT-BECOMES-BVNTH-FOR-NATPS-hack
;;   (IMPLIES (AND (all-unsigned-byte-p 4 vals)
;;                 ;(ALL-NATP VALS)
;;                 (NATP HIGHSIZE)
;;                 (NATP LOWSIZE)
;;                 (< (BVCAT HIGHSIZE HIGHVAL LOWSIZE LOWVAL) (LEN VALS))
;;                 )
;;            (EQUAL (NTH (BVCAT HIGHSIZE HIGHVAL LOWSIZE LOWVAL) VALS)
;;                   (BVNTH 4
;;                          (+ HIGHSIZE LOWSIZE)
;;                          (BVCAT HIGHSIZE HIGHVAL LOWSIZE LOWVAL)
;;                          VALS)))
;;   :HINTS
;;   (("Goal"
;;     :IN-THEORY (E/d (BVNTH BV-ARRAY-READ
;;                        ALL-INTEGERP-WHEN-ALL-NATP) (NTH-OF-BVCAT-BECOMES-BVNTH-FOR-NATPS)))))


;how can we easily turn a nest of conses into a nest of bv-array-write calls?

;main rule for handling a nest of conses - gen the 4...
;will this loop?
;yeah, probably
;; (defthmd cons-becomes-bv-array-write-size-4-gen
;;   (implies (and (unsigned-byte-p 4 a)
;;                 (all-unsigned-byte-p 4 lst)
;;                 (true-listp lst)
;;                 )
;;            (equal (cons a lst)
;;                   (bv-array-write 4 (+ 1 (len lst)) 0 a (cons 0 lst))))
;;   :hints (("Goal" :in-theory (enable update-nth2))))

(defthmd cons-a-into-singleton-0-size-4
  (implies (unsigned-byte-p 4 a)
           (equal (cons a '(0))
                  (bv-array-write 4 2 0 a '(0 0))))
  :hints (("Goal" :in-theory (enable bv-array-write update-nth2))))

;bboz here we guess that the size is 1 - gross?
(defthmd cons-a-onto-constant-size-1-becomes-bv-array-write
  (implies (and (syntaxp (quotep data))
                (all-unsigned-byte-p 1 data)
                (true-listp data)
                (unsigned-byte-p 1 a))
           (equal (cons a data)
                  (bv-array-write 1 (+ 1 (len data)) 0 a (cons 0 data))))
  :hints (("Goal" :in-theory (enable bv-array-write update-nth2))))

(defthmd cons-a-onto-constant-size-4-becomes-bv-array-write
  (implies (and (syntaxp (quotep data))
                (true-listp data)
                (all-unsigned-byte-p 4 data)
                (unsigned-byte-p 4 a))
           (equal (cons a data)
                  (bv-array-write 4 (+ 1 (len data)) 0 a (cons 0 data))))
  :hints (("Goal" :in-theory (enable bv-array-write update-nth2))))

(defthmd cons-a-onto-constant-size-8-becomes-bv-array-write
  (implies (and (syntaxp (quotep data))
                (true-listp data)
                (all-unsigned-byte-p 8 data)
                (unsigned-byte-p 8 a))
           (equal (cons a data)
                  (bv-array-write 8 (+ 1 (len data)) 0 a (cons 0 data))))
  :hints (("Goal" :in-theory (enable bv-array-write update-nth2))))

(defthm bv-array-read-of-myif
  (equal (bv-array-read esize len index (myif test x y))
         (myif test (bv-array-read esize len index x) (bv-array-read esize len index y)))
  :hints (("Goal" :in-theory (enable myif))))

(defthm bvif-of-bv-array-read-tighten-arg1
  (implies (and (< size1 size2)
                (natp size1)
                (natp size2))
           (equal (bvif size1 test (bv-array-read size2 len index data) z)
                  (bvif size1 test (bv-array-read size1 len index data) z)))
  :hints (("Goal" :in-theory (e/d (bvif myif bv-array-read)
                                  (;;MYIF-OF-GETBIT-BECOMES-BVIF-ARG2 MYIF-OF-GETBIT-BECOMES-BVIF-ARG1
                                   )))))

(defthm bvif-of-bv-array-read-tighten-arg2
  (implies (and (< size1 size2)
                (natp size1)
                (natp size2))
           (equal (bvif size1 test z (bv-array-read size2 len index data))
                  (bvif size1 test z (bv-array-read size1 len index data))))
  :hints (("Goal" :in-theory (e/d (bvif myif bv-array-read)
                                  (;;MYIF-OF-GETBIT-BECOMES-BVIF-ARG2 MYIF-OF-GETBIT-BECOMES-BVIF-ARG1
                                   )))))

;; (defthm nth-becomes-bvnth-when-unsigned-byte-p
;;   (implies (and (unsigned-byte-p size index) ;size is a free variable
;;                 (all-natp vals)
;;                 (<= (expt 2 size) (len vals)))
;;            (equal (nth index vals)
;;                   (bvnth (width-of-widest-int vals)
;;                          size
;;                          index
;;                          vals)))
;;   :hints (("Goal" :in-theory (enable bvnth all-integerp-when-all-natp))))

;go get the length of the lists (using a binding hyp??)
(defthmd nth-becomes-bv-array-read
  (implies (and (syntaxp (quotep vals))
                (all-natp vals)
                (< index (len vals))
                (natp index))
           (equal (nth index vals)
                  (bv-array-read (width-of-widest-int vals) (len vals) index vals)))
  :hints (("Goal" :in-theory (enable BV-ARRAY-READ ;bvnth
                                     ceiling-of-lg))))

;compare to nth-becomes-bv-array-read-strong
(defthmd nth-becomes-bv-array-read-strong2
  (implies (and (syntaxp (quotep vals))
                (all-natp vals))
           (equal (nth index vals)
                  (if (not (natp index))
                      (car vals)
                    (if (< index (len vals))
                        (bv-array-read (width-of-widest-int vals) (len vals) index vals)
                      nil))))
  :hints (("Goal" :use (:instance nth-becomes-bv-array-read)
           :in-theory (disable nth-becomes-bv-array-read))))

(defthm bvchop-of-bv-array-read-old
  (implies (and (<= n element-size)
                (natp n)
                (natp index)
                (< 0 len)
                (equal len (len data))
                (all-integerp data)
                (integerp element-size))
           (equal (bvchop n (bv-array-read element-size len index data))
                  (bv-array-read n len (bvchop (integer-length (+ -1 len))
                                                index)
                                 (bvchop-list n data))))
  :hints (("Goal" :in-theory (enable bv-array-read ceiling-of-lg))))

;;from des encrypt sun:

;bozo be more systematic about stuff like this
(defthm bv-array-write-of-bvif-tighten
  (implies (and (< size size2) ;would loop if =
                (natp size)
                (natp size2)
                (natp index)
                (integerp x) ;drop
                (integerp y) ;drop
                (equal length (len array))
                (< index length) ;drop?
                )
           (equal (bv-array-write size length index (bvif size2 test x y) array)
                  (bv-array-write size length index (bvif size test x y) array)))
  :hints (("Goal" :in-theory (enable bv-array-write update-nth2))))

;(local (in-theory (enable unsigned-byte-p-forced))) ;yuck?

(defthmd bv-array-read-trim-element-size
  (implies (and (syntaxp (quotep data))
                (< (width-of-widest-int data) element-size)
                (natp index)
                (< index (len data))
                (natp element-size)
                (equal len (len data))
                (all-natp data)
                )
           (equal (bv-array-read element-size len index data)
                  (bv-array-read (width-of-widest-int data) len index data)))
  :hints (("Goal"
           :use (:instance unsigned-byte-p-of-width-of-widest-int-nth (vals data))
           :in-theory (e/d (bv-array-read-opener) (unsigned-byte-p-of-width-of-widest-int-nth
                                                   all-unsigned-byte-p-of-width-of-widest-int)))))

;bozo use this more
;can be expensive (e.g., if val is a bvcat and the value already there is a constant - then we split the bvcat, etc.)
(defthmd bv-array-write-does-nothing
  (implies (and (syntaxp (quotep val))
                (equal val (bv-array-read element-size len key lst))
                (equal len (len lst))
                (natp key)
                (< key (len lst)))
           (equal (bv-array-write element-size len key val lst)
                  (bvchop-list element-size lst)))
  :hints (("Goal" :in-theory (e/d (bv-array-write bv-array-read update-nth2
                                                  ;list::update-nth-equal-rewrite
                                                  BVCHOP-WHEN-I-IS-NOT-AN-INTEGER
                                                  update-nth-when-equal-of-nth
                                                  )
                                  ( ;take-of-bvchop-list
                                   )))))

;; ;just use a trim rule?
;; (defthm bvxor-of-bad-constant
;;   (implies (and (syntaxp (quotep x))
;;                 (syntaxp (quotep size))
;;                 (not (unsigned-byte-p size x))
;;                 (integerp size)
;;                 (< 0 size)
;;                 ;(integerp x)
;;                 ;(integerp y)
;;                 )
;;            (equal (bvxor size x y)
;;                   (bvxor size (bvchop size x) y)))
;;   :hints (("Goal" :in-theory (enable))))

;(local (in-theory (disable jvm::int-lemma0))) ;could make a cheap version with a free var

;; (defthm bvchop-of-bvnth
;;   (implies (and (<= n element-size)
;;                 (natp n)
;;                 (natp element-size))
;;            (equal (bvchop n (bvnth element-size index-size index data))
;;                   (bvnth n index-size index data)))
;;   :hints (("Goal" :in-theory (enable bvnth))))

(defthm bv-array-read-of-subrange
  (implies (and (natp index)
                (natp start)
                (<= start end)
                (integerp end)
                (< index len)
                (equal len (+ end 1 (- start)))
                (< end (len lst))
                (natp element-size)
                )
           (equal (bv-array-read element-size len index (subrange start end lst))
                  (bv-array-read element-size (+ 1 end) (+ start index) lst)))
  :hints (("Goal" :in-theory (enable bv-array-read-opener bvchop-when-i-is-not-an-integer subrange))))

;; (defthm logext-list-of-myif-of-logext-list-arg2
;;   (equal (logext-list 8 (myif test x (logext-list 8 y)))
;;          (logext-list 8 (myif test x y)))
;;   :hints (("Goal" :in-theory (enable myif))))

;; (defthm logext-list-of-myif-of-logext-list-arg1
;;   (equal (logext-list 8 (myif test (logext-list 8 y) x))
;;          (logext-list 8 (myif test y x)))
;;   :hints (("Goal" :in-theory (enable myif))))

;; ;bozo hack.  replace with a general thing that pushed a bvchop-list down a myif nest
;; (defthm bv-array-write-of-myif-of-logext-list
;;   (implies (and (< index len)
;;                 (natp len)
;;                 (natp width)
;;                 (natp index))
;;            (equal (bv-array-write width len index val (myif y z (logext-list width w)))
;;                   (bv-array-write width len index val (myif y z w))))
;;   :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;            :in-theory (e/d (myif bv-array-write update-nth2
;;                                  take
;;                                  SUBRANGE nthcdr LOGEXT-LIST
;;                                  )
;;                            (TRUE-LISTP-WHEN-NOT-CONSP
;;                             NTHCDR-OF-CDR-COMBINE-STRONG
;;                             TAKE-OF-CDR-BECOMES-SUBRANGE
;;                             NTHCDR-OF-TAKE-BECOMES-SUBRANGE
;;                             SUBRANGE-TO-END-BECOMES-NTHCDR)))))

;; ;should we keep pushing it, or stop? might as well keep pushing it?
;; (defthm push-bvchop-list-of-logext-list
;;   (implies (and (<= size2 size1)
;;                 (natp size2)
;;                 (integerp size1))
;;            (equal (push-bvchop-list size2 (logext-list size1 lst))
;;                   (push-bvchop-list size2 lst))))

;; ;i hope this isn't a disaster (perhaps store the whole path of nodes we want this to walk down)?
;; ;or perhaps have two phases (copy the push-bvchop-list to every node of the if nest, then remove it?)
;; (defthm push-bvchop-list-of-myif
;;   (equal (push-bvchop-list size (myif test x y))
;;          (myif test (push-bvchop-list size x) (push-bvchop-list size y)))
;;   :hints (("Goal" :in-theory (enable myif))))

;; (defthm push-bvchop-list-of-bv-array-write
;;   (implies (and (<= size size2)
;;                 (natp size)
;;                 (integerp size2))
;;            (equal (push-bvchop-list size2 (bv-array-write size len index val lst))
;;                   (bv-array-write size len index val lst)))
;;   :hints (("Goal" :in-theory (enable bv-array-write))))

;; (defthm push-bvchop-list-of-push-bvchop-list
;;   (implies (and (<= size size2)
;;                 (natp size)
;;                 (integerp size2))
;;            (equal (push-bvchop-list size2 (push-bvchop-list size lst))
;;                   (push-bvchop-list size lst)))
;;   :hints (("Goal" :in-theory (enable bv-array-write))))

(defthm bv-array-read-of-bv-array-write-tighten2
  (implies (and (< width2 width1) ;if we allow =, it will loop
                (natp width2)
                (natp len)
                (< 0 len) ;bozo
                (natp index)
                (natp index2)
                (integerp width1))
           (equal (bv-array-read width1 len index (bv-array-write width2 len index2 val lst))
                  (bv-array-read width2 len index (bv-array-write width2 len index2 val lst))))
  :hints (("Goal" :in-theory (e/d (bv-array-read bv-array-write
                                                 BVCHOP-WHEN-I-IS-NOT-AN-INTEGER)
                                  (;BVCHOP-LIST-OF-TAKE
                                   )))))

;(local (in-theory (disable LIST::UPDATE-NTH-EQUAL-REWRITE)))

;bozo where does the firstn arise?  arraycopy?
(defthm firstn-of-bv-array-write
  (implies (and (<= len1 len2)
                (< index len1) ;Mon Jul 19 20:31:52 2010
                (natp len1)
                (natp index)
                (integerp len2))
           (equal (firstn len1 (bv-array-write width len2 index val lst))
                  (bv-array-write width len1 index val lst)))
  :hints (("Goal" :in-theory (e/d (bv-array-write-opener update-nth2 natp
                                                         ;;take
                                                         ;<-of-if-arg1
                                                         )
                                  (;bvchop-list-of-take
                                   )))))

(defthm bv-array-read-of-bvchop-list-tighten
  (implies (and (< 0 len)
                (integerp len)
                (natp index)
                (< index len)
                (<= width2 width1) ;handle the other case?
                (natp width2)
                (integerp width1)
                )
           (equal (bv-array-read width1 len index (bvchop-list width2 lst))
                  (bv-array-read width2 len index lst)))
  :hints (("Goal" :in-theory (enable bv-array-read bvchop-when-i-is-not-an-integer))))

;; (defthmd nth2-becomes-bvnth-for-natps-dag
;;   (implies (and (syntaxp (quotep vals))
;;                 (all-natp vals)
;;                 (natp indexsize)
;;                 (natp index)
;;                 (< index (len vals))
;;                 )
;;            (equal (nth2 indexsize index vals)
;;                   (bvnth (width-of-widest-int vals)
;;                          indexsize
;;                          index
;;                          vals)))
;;   :hints (("Goal"
;;            :cases ((<= (bvchop indexsize index) index))
;;            :in-theory (enable nth2 bvnth all-integerp-when-all-natp))))

;bvchop analogue?
(defthm bv-array-read-of-getbit-when-len-is-2
  (equal (bv-array-read element-size 2 (getbit 0 x) lst)
         (bv-array-read element-size 2 x lst))
  :hints (("Goal" :in-theory (enable bv-array-read bvchop-when-i-is-not-an-integer getbit-when-val-is-not-an-integer getbit))))

;; (defthm take-of-logext-list
;;   (implies (and (<= n (len lst)) (natp n))
;;            (equal (take n (logext-list size lst))
;;                   (logext-list size (take n lst))))
;;   :hints (("Goal" :in-theory (e/d (take logext-list) (take-of-cdr-becomes-subrange)))))


(DEFTHM GETBIT-LIST-OF-BV-ARRAY-WRITE-too-high
  (IMPLIES (AND (>= N ESIZE)
                (EQUAL LEN (LEN LST))
                (< KEY LEN)
                (NATP N)
                (NATP ESIZE)
                (NATP KEY)
                (NATP LEN))
           (EQUAL (GETBIT-LIST N (BV-ARRAY-WRITE ESIZE LEN KEY VAL LST))
                  (repeat len 0))))

;; (thm
;;  (implies (and (equal (len x) (max (+ 1 (nfix key)) (len l)))
;;                (natp key))
;;           (equal (myif test x (jvm::update-nth-local key val l))
;;                  (jvm::update-nth-local key (myif test (nth key x) val) (myif test x l))))
;;  :hints (("Goal" :in-theory (e/d (len-update-nth myif list::update-nth-equal-rewrite nth-when-n-is-zp) (car-becomes-nth-of-0)))))


;; here we are bit-blasting the index
(local
  (defthmd bv-array-read-blast-one-step-helper
    (implies (and (equal len (expt 2 index-width))
                  (posp index-width)
                  (natp index))
             (equal (bv-array-read element-size len index vals)
                    (bvif element-size
                          (equal 1 (getbit (+ -1 index-width) index))
                          (bv-array-read element-size (expt 2 (+ -1 index-width))
                                         (bvchop (+ -1 index-width) index)
                                         (subrange (expt 2 (+ -1 index-width))
                                                   (+ -1 (expt 2 index-width))
                                                   vals))
                          (bv-array-read element-size (expt 2 (+ -1 index-width))
                                         (bvchop (+ -1 index-width) index)
                                         (subrange 0 (+ -1 (expt 2 (+ -1 index-width)))
                                                   vals)))))
    :hints (("Goal"
             :use (;; (:instance BVCAT-SPECIAL-OPENER
                   ;;                           (x (getbit (+ -1 index-width) index))
                   ;;                           (y (bvchop (+ -1 index-width) index))
                   ;;                           (n (+ -1 index-width)))
                   (:instance BVCAT-OF-GETBIT-AND-X-ADJACENT
                              (n (+ -1 index-width))
                              (x index)))
;          :expand ((BVCAT 1 0 7 INDEX))
             :in-theory (e/d (subrange
                              bvif
                              bv-ARRAY-READ
                              ;;LOGAPP-0
                              ceiling-of-lg
                              bvcat logapp)
                             (BVCAT-OF-GETBIT-AND-X-ADJACENT
                              TIMES-4-BECOMES-LOGAPP
                              BVCAT-OF-GETBIT-AND-X-ADJACENT
                              BVCAT-EQUAL-REWRITE BVCAT-EQUAL-REWRITE-alt
                              LOGAPP-EQUAL-REWRITE
                              BVCAT-OF-0-arg2
                              ))))))

;actually matches
(defthmd bv-array-read-blast-one-step
  (implies (and (equal len (expt 2 (+ -1 (integer-length len))))

                (<= 2 len)
                (natp index))
           (equal (bv-array-read element-size len index vals)
                  (bvif element-size
                        (equal 1 (getbit (+ -1 (+ -1 (integer-length len))) index))
                        (bv-array-read element-size
                                       (expt 2 (+ -1 (+ -1 (integer-length len))))
                                       (bvchop (+ -1 (+ -1 (integer-length len))) index)
                                       (subrange (expt 2 (+ -1 (+ -1 (integer-length len)))) (+ -1 (expt 2 (+ -1 (integer-length len)))) vals))
                        (bv-array-read element-size
                                       (expt 2 (+ -1 (+ -1 (integer-length len))))
                                       (bvchop (+ -1 (+ -1 (integer-length len))) index)
                                       (subrange 0 (+ -1 (expt 2 (+ -1 (+ -1 (integer-length len))))) vals)))))
  :hints (("Goal" :use (:instance bv-array-read-blast-one-step-helper (index-width (+ -1 (integer-length len)))))))

;; (thm
;;  (implies (and (EQUAL (CDR LST) (CDR RHS))
;;                (consp lst)
;;                (consp rhs))
;;           (EQUAL (LEN LST) (LEN RHS)))
;;  :hints (("Goal" :in-theory (e/d (len) (LEN-OF-CDR-BETTER LIST::LEN-OF-CDR)))))

(defthm bv-array-write-equal-rewrite
  (implies (and (natp esize)
                (natp key)
                (< key len)
                (natp len)
                (all-unsigned-byte-p esize lst)
                (all-unsigned-byte-p esize rhs) ;new
                (equal len (len lst))
                (true-listp lst)
                (TRUE-LISTP RHS) ;new
                )
           (equal (equal (bv-array-write esize len key val lst)
                         rhs)
                  (and (equal len (len rhs))
                       (true-listp rhs)
                       (all-unsigned-byte-p esize rhs)
                       (equal (bvchop esize val)
                              (bv-array-read esize len key rhs))
                       (equal (bv-array-clear esize len key lst)
                              (bv-array-clear esize len key rhs)))))
  :hints (("Goal" :cases ((equal (+ 1 KEY) (len rhs)))
           :in-theory (e/d (BV-ARRAY-CLEAR bv-array-write BV-ARRAY-READ update-nth2
                                           UPDATE-NTH-WHEN-EQUAL-OF-NTH
                                           equal-of-update-nth-new)
                           (UPDATE-NTH-BECOMES-UPDATE-NTH2-EXTEND-GEN)))))

;; (defthm bv-array-write-equal-rewrite
;;   (implies (and (natp esize)
;;                 (natp key)
;;                 (< key len)
;;                 (natp len)
;;                 (all-unsigned-byte-p esize lst)
;;                 (equal len (len lst))
;;                 (true-listp lst))
;;            (equal (equal (bv-array-write esize len key val lst)
;;                          rhs)
;;                   (and (equal len (len rhs))
;;                        (true-listp rhs)
;;                        (all-unsigned-byte-p esize rhs)
;;                        (equal (bvchop esize val)
;;                               (bv-array-read esize len key rhs))
;;                        (equal (bv-array-clear esize len key lst)
;;                               (bv-array-clear esize len key rhs)))))
;;   :hints ((and stable-under-simplificationp
;;                '(:use ((:instance update-nths-equal-when-clear-nths-equal (key (+ -1 key))
;;                                   (l1 (cdr rhs))
;;                                   (l2 (cdr lst))
;;                                   (val (BVCHOP ESIZE VAL))
;;                                   )
;;                        (:instance equal-of-lens-when-equal-of-clear-nths
;;                                   (x (cdr lst)) (y (cdr rhs))
;;                                   (n (+ -1 key))))
;;                       :expand ( ;(LEN LST)
;;     ;(LEN cdr)
;;                                (ALL-UNSIGNED-BYTE-P ESIZE LST)
;;                                (ALL-UNSIGNED-BYTE-P ESIZE RHS))
;;                       :in-theory (e/d (EQUAL-CONS-CASES2-ALT-BETTER)
;;                                       (equal-of-lens-when-equal-of-clear-nths
;;                                        list::len-of-cdr
;;                                        list::len-of-cdr-better
;;                                        ))))
;;           ("Goal" :do-not '(generalize eliminate-destructors)

;;            :in-theory (e/d (bv-array-write UPDATE-NTH2 BV-ARRAY-READ-opener
;;                                            LIST::UPDATE-NTH-EQUAL-REWRITE
;;                                            LIST::NTH-OF-CONS
;;                                            bv-array-clear)
;;                            (
;;                             EQUAL-CONS-CASES2-ALT-BETTER ;new
;;                             UPDATE-NTH-BECOMES-UPDATE-NTH2-EXTEND-GEN
;;                             BVCHOP-LIST-OF-TAKE
;;                             )))))

(defthm bv-array-write-equal-rewrite-alt
  (implies (and (natp esize)
                (natp key)
                (< key len)
                (natp len)
                (all-unsigned-byte-p esize lst)
                (all-unsigned-byte-p esize rhs)
                (equal len (len lst))
                (true-listp lst)
                (true-listp rhs)
                )
           (equal (equal rhs
                         (bv-array-write esize len key val lst))
                  (and (equal len (len rhs))
                       (true-listp rhs)
                       (all-unsigned-byte-p esize rhs)
                       (equal (bvchop esize val)
                              (bv-array-read esize len key rhs))
                       (equal (bv-array-clear esize len key lst)
                              (bv-array-clear esize len key rhs)))))
  :hints (("Goal" :use (:instance bv-array-write-equal-rewrite)
           :in-theory (disable bv-array-write-equal-rewrite))))

;move
;do we trim array reads?
(defthm trim-of-bv-array-read
  (equal (trim n (bv-array-read element-size len index data))
         (bv-array-read (min (nfix n) (ifix element-size)) len index data))
  :hints (("Goal" :in-theory (enable trim natp bvchop-of-bv-array-read))))

;; (thm
;;  (IMPLIES (and (EQUAL free (BVCHOP 5 X))
;;                (syntaxp (and (quotep free)
;;                              (not (quotep x)))))
;;           (EQUAL (BVSHL 32 X SHIFT-AMOUNT)
;;                  (BVSHL 32 free SHIFT-AMOUNT)))
;;  :hints (("Goal" :in-theory (enable bvshl))))

;what do we want to happen in this case?
;; (defthm bv-array-read-when-arg3-negative
;;   (implies (< arg3 0)
;;            (equal (bv-array-read arg1 arg2 arg3 arg4)
;;                   (bv-array-read arg1 arg2 0 arg4)))
;;   :hints (("Goal" :in-theory (enable bv-array-read))))

;; (defthmd nth-unroll
;;   (implies (not (zp n))
;;            (equal (nth n l)
;;                   (nth (- n 1) (cdr l)))))

;; (defthm bv-array-read-of-logext-list-gen
;;   (implies (and (<= size size2)
;;                 (equal len (len lst))
;;                 (natp size)
;;                 (integerp size2))
;;            (equal (bv-array-read size len index (logext-list size2 lst))
;;                   (bv-array-read size len index lst)))
;;   :hints
;;   (("Goal" :cases ((equal 0 (len lst))) ;yuck
;;     :in-theory (e/d (bvchop-when-i-is-not-an-integer
;;                        bv-array-read) ()))))


;move
;change for ACL2 4.3
;; (defthm member-becomes-member-equal
;;   (equal (member x lst)
;;          (member-equal x lst))
;;   :hints (("Goal" :in-theory (enable member-equal member))))


;; (thm
;;  (implies (integerp n)
;;           (equal (< n (logext 32 (+ 1 n)))
;;                  (not (equal (bvchop 32 n) 2147483647))))
;;  :hints (("Goal" :in-theory (e/d (logext logapp getbit slice)
;;                                  (LOGTAIL-OF-BVCHOP-BECOMES-SLICE
;;                                                          SLICE-BECOMES-BVCHOP
;;                                                          )))))

(defthm bv-array-read-of-logext-arg3
  (implies (and (integerp index)
                (integerp width2)
                (<= (integer-length (+ -1 len)) width2))
           (equal (bv-array-read width len (logext width2 index) data)
                  (bv-array-read width len index data)))
  :hints (("Goal" :in-theory (enable bv-array-read ceiling-of-lg))))


;; (thm
;;  (implies (integerp x)
;;           (equal (< (JVM::IDIV x '4) '0)
;;                  (< x -4)))
;;  :hints (("Goal" :in-theory (enable JVM::IDIV))))



;; (implies (and (<= 0 (jvm::idiv i 4))
;;               (<= 0 i))
;;          (<= 0 (jvm::idiv (logext 32 (+ -1 i)) 4)))


;fixme prove a lemma about BV-ARRAY-WRITE with an out of bound index
(DEFTHM BV-ARRAY-WRITE-OF-LOGEXT-AROUND-VALUE-gen
  (IMPLIES (AND (<= ELEMENT-SIZE SIZE)
                (NATP SIZE)
                (NATP ELEMENT-SIZE)
                (< key len) ;Mon Jul 19 20:36:57 2010
                (NATP LEN)
                (NATP KEY))
           (EQUAL (BV-ARRAY-WRITE ELEMENT-SIZE LEN KEY (LOGEXT SIZE VAL) LST)
                  (BV-ARRAY-WRITE ELEMENT-SIZE LEN KEY VAL LST)))
  :hints (("Goal" :cases ((< KEY LEN))
           :use (:instance BV-ARRAY-WRITE-OF-LOGEXT-AROUND-VALUE)
           :in-theory (e/d (BV-ARRAY-WRITE) (BV-ARRAY-WRITE-OF-LOGEXT-AROUND-VALUE)))))

(defthm equal-nil-of-myif
  (implies (and (not (equal nil a))
                (not (equal nil b)))
           (equal (equal nil (myif test a b))
                  nil)))

;;(ALL-UNSIGNED-BYTE-P 0 X2)

;consider (subrange 10 100 (bv-array-write 8 16 4 5 '(0 0 0 0 0 0 0 0)))
(defthm subrange-of-bv-array-write-irrel-1
  (implies (and (< index low) ;this case
                (< high len) ;handle?
                (natp len)
                (natp high)
                (natp index)
                (integerp low))
           (equal (subrange low high (bv-array-write width len index val data))
                  (subrange low high (bvchop-list width (take len data)))
                  ))
  :hints (("Goal" :cases ((<= low high))
           :in-theory (e/d (bv-array-write update-nth2
                                           subrange ;bozo?
                                           ceiling-of-lg
                                           bvchop-list-of-nthcdr
                                           TAKE-OF-NTHCDR
                                           )
                           (;anti-subrange
                            NTHCDR-OF-TAKE
                            NTHCDR-OF-BVCHOP-LIST
                            NTHCDR-OF-BVCHOP-LIST-better

                            ;CDR-OF-TAKE-BECOMES-SUBRANGE-BETtER ;bozo ;also bozo on the non better
                            UPDATE-NTH-BECOMES-UPDATE-NTH2-EXTEND-GEN)))))

(defthm subrange-of-bv-array-write-irrel-2
  (implies (and (< high index) ;this case
                (< high len) ;handle?
                (< index len)
                (natp len)
                (natp high)
                (natp index)
                (integerp low)
                )
           (equal (subrange low high (bv-array-write width len index val data))
                  (subrange low high (bvchop-list width (take len data)))))
  :hints (("Goal" :cases ((<= low high))
           :in-theory (e/d (bv-array-write-opener
                            update-nth2
                            subrange ;bozo?
                            )
                           (;anti-subrange
                            UPDATE-NTH-BECOMES-UPDATE-NTH2-EXTEND-GEN)))))



(defthm equal-of-nth-and-bv-array-read
  (implies (and (<= len (len x))
                (all-unsigned-byte-p size x)
                (natp n)
                (natp len)
                (< n len) ;move
                )
           (equal (equal (nth n x) (bv-array-read size len n x))
                  t))
  :hints (("Goal" :in-theory (enable bv-array-read-opener))))

(defthm equal-of-nth-and-bv-array-read-alt
  (implies (and (<= len (len x))
                (all-unsigned-byte-p size x)
                (natp n)
                (natp len)
                (< n len) ;move
                )
           (equal (equal (bv-array-read size len n x) (nth n x))
                  t))
  :hints (("Goal" :use (:instance equal-of-nth-and-bv-array-read)
           :in-theory (disable equal-of-nth-and-bv-array-read))))

(defthmd equal-of-bvchop-of-nth-and-bv-array-read-helper
  (implies (and (<= len (len x))
                (natp len)
                (< n len)
                (natp n))
           (equal (equal (bvchop size (nth n x)) (bv-array-read size len n x))
                  t))
  :hints (("Goal" :in-theory (enable bv-array-read-opener))))

(defthm equal-of-bvchop-of-nth-and-bv-array-read
  (implies (and (equal len (len x)) ;relax?
                (natp len)
                (natp n))
           (equal (equal (bvchop size (nth n x)) (bv-array-read size len n x))
                  (if (< n len)
                      t
                    (equal 0 (bv-array-read size len n x)))))
  :hints (("Goal" :use (:instance equal-of-bvchop-of-nth-and-bv-array-read-helper)
           :in-theory (disable equal-of-bvchop-of-nth-and-bv-array-read-helper))))

(defthm equal-of-bvchop-of-nth-and-bv-array-read-alt
  (implies (and (equal len (len x))
                (natp n))
           (equal (equal (bv-array-read size len n x) (bvchop size (nth n x)))
                  (if (< n len)
                      t
                    (equal 0 (bv-array-read size len n x)))))
  :hints (("Goal" :use (:instance equal-of-bvchop-of-nth-and-bv-array-read)
           :in-theory (disable equal-of-bvchop-of-nth-and-bv-array-read))))

;note the (equal m n) hyp
(defthm equal-of-bvchop-of-nth-and-bv-array-read-alt-strong
  (implies (and (equal m n)
                (equal len (len x)) ;work-hard or relax?
                (natp n))
           (equal (equal (bv-array-read size len n x) (bvchop size (nth m x)))
                  (if (< n len)
                      t
                    (equal 0 (bv-array-read size len n x))))))

;note the (equal m n) hyp
(defthm equal-of-bvchop-of-nth-and-bv-array-read-strong
  (implies (and (equal m n)
                (equal len (len x)) ;work-hard or relax?
                (natp n))
           (equal (equal (bvchop size (nth m x)) (bv-array-read size len n x))
                  (if (< n len)
                      t
                    (equal 0 (bv-array-read size len n x))))))

;; (defstub error-state-no-params () t)

;; ;fixme - handle this stuff better?
;; (skip -proofs
;;  (defthm error-state-drop-params
;;    (equal (jvm::error-state msg state)
;;           (error-state-no-params))))

;(in-theory (disable CDR-OF-TAKE-BECOMES-SUBRANGE)) ;drop?

;gen!
;; (defthm nth2-of-bv-array-write
;;   (implies (and (natp index)
;;                 (< index 64)
;;                 )
;;            (equal (nth2 '6 index (bv-array-write '16 '64 index2 val array))
;;                   (bv-array-read '16 '64 index (bv-array-write '16 '64 index2 val array))))
;;   :hints (("Goal" :in-theory (enable ;BV-ARRAY-READ
;;                               nth2))))

(DEFTHM BV-ARRAY-READ-OF-BV-ARRAY-WRITE-TIGHTEN-better
  (IMPLIES (AND (< ESIZE1 ESIZE2)
                (EQUAL LEN (LEN DATA))
                (NATP INDEX2)
                (NATP ESIZE1)
                (NATP ESIZE2)
                (NATP INDEX))
           (EQUAL (BV-ARRAY-READ ESIZE1 LEN INDEX (BV-ARRAY-WRITE ESIZE2 LEN INDEX2 VAL DATA))
                  (BV-ARRAY-READ ESIZE1 LEN INDEX (BV-ARRAY-WRITE ESIZE1 LEN INDEX2 VAL DATA))))
  :HINTS
  (("Goal"
    :IN-THEORY (E/d (BV-ARRAY-READ BV-ARRAY-WRITE update-nth2
                     BVCHOP-WHEN-I-IS-NOT-AN-INTEGER)
                    (;BVCHOP-OF-NTH-BECOMES-BV-ARRAY-READ
                     UPDATE-NTH-BECOMES-UPDATE-NTH2-EXTEND-GEN
                     )))))

;move a bunch of this stuff

(defthmd subrange-when-take-known-hack
  (implies (and (equal (take n x) free)
                (integerp n)
                )
           (equal (subrange 1 n x)
                  (if (posp n)
                      (append (cdr free) (list (nth n x)))
                    nil)))
  :hints (("Goal" :in-theory (enable equal-of-append
                                     subrange ;todo
                                     ))))

(defthm bv-array-clear-bottom-range
  (implies (and (posp len)
                (< i len)
                (natp i))
           (equal (bv-array-clear-range elem-size len 0 i lst)
                  (append (repeat (+ 1 i) 0)
                          (bvchop-list elem-size (subrange (+ 1 i) (+ -1 len) lst)))))
  :hints (("Goal" :cases ((equal 0 i))
           :in-theory (e/d (subrange TAKE-OF-CDR CAR-BECOMES-NTH-OF-0 equal-of-append nthcdr-of-cdr-combine
                                            BV-ARRAY-CLEAR-RANGE)
                                  (cdr-of-take
                                   ;NTHCDR-OF-TAKE-BECOMES-SUBRANGE
                                   ;;TAKE-OF-CDR-BECOMES-SUBRANGE
                                   )))))

(defthm bv-array-clear-whole-range
  (implies (and (equal i (+ -1 len))
                (posp len))
           (equal (bv-array-clear-range elem-size len 0 i lst)
                  (repeat len 0)))
  :hints (("Goal" :in-theory (e/d (equal-of-append subrange)
                                  (bv-array-clear-bottom-range))
           :use (:instance bv-array-clear-bottom-range
                           (lst (true-list-fix lst))
                           (i (+ -1 len))))))

(defthm bv-array-write-of-firstn
  (equal (bv-array-write element-size len index val (firstn len data))
         (bv-array-write element-size len index val data))
  :hints (("Goal" :in-theory (e/d (bv-array-write update-nth2) (update-nth-becomes-update-nth2-extend-gen)))))

(defthm bv-array-clear-of-firstn
  (equal (bv-array-clear element-size len index (firstn len data))
         (bv-array-clear element-size len index data))
  :hints (("Goal" :in-theory (enable bv-array-clear))))

(defthm bv-array-read-of-bv-array-clear
  (implies (and (< index1 len)
                (< index2 len) ;Mon Jul 19 20:51:20 2010
                (natp width2)
                (<= width width2)
                (posp len)
                (natp index1)
                (natp index2)
                (integerp len))
           (equal (bv-array-read width len index1 (bv-array-clear width2 len index2 lst))
                  (if (not (equal index1 index2))
                      (bv-array-read width len index1 lst)
                    0)))
  :hints (("Goal" :in-theory (enable bv-array-clear))))

(defthm bv-array-read-of-bv-array-clear-range-low
  (implies (and (< index lowindex)
                (< highindex len)
                (<= lowindex highindex)
                (natp elem-size)
                (natp len)
                (natp index)
                (natp lowindex)
                (natp highindex))
           (equal (bv-array-read elem-size len index (bv-array-clear-range elem-size len lowindex highindex lst))
                  (bv-array-read elem-size len index lst)))
  :hints (("Goal" :expand ((BV-ARRAY-CLEAR-RANGE ELEM-SIZE LEN INDEX1 HIGHINDEX LST))
           :in-theory (enable bv-array-clear-range))))

(defthm bv-array-read-of-bv-array-clear-range-high
  (implies (and (< highindex index)
                (< highindex len)
                (<= lowindex highindex)
                (< index len)
                (natp elem-size)
                (natp len)
                (natp index)
                (natp lowindex)
                (natp highindex))
           (equal (bv-array-read elem-size len index (bv-array-clear-range elem-size len lowindex highindex lst))
                  (bv-array-read elem-size len index lst)))
  :hints (("Goal" :expand ((BV-ARRAY-CLEAR-RANGE ELEM-SIZE LEN INDEX1 HIGHINDEX LST))
           :in-theory (enable bv-array-clear-range))))

(defthm bv-array-read-of-bv-array-clear-range-contained
  (implies (and (<= lowindex index)
                (<= index highindex)
                (< highindex len)
                (<= lowindex highindex)
                (natp elem-size)
                (natp len)
                (natp index)
                (natp lowindex)
                (natp highindex))
           (equal (bv-array-read elem-size len index (bv-array-clear-range elem-size len lowindex highindex lst))
                  0))
  :hints (("Goal" :expand ((BV-ARRAY-CLEAR-RANGE ELEM-SIZE LEN INDEX HIGHINDEX LST))
           :in-theory (enable bv-array-clear-range))))

;move these
;a hack for rc2, since we are no longer trimming array reads
(defthm bvplus-of-bv-array-read-arg1
  (implies (and (< n element-size)
                (natp n)
                (integerp element-size))
           (equal (bvplus n (bv-array-read element-size len index data) y)
                  (bvplus n (bv-array-read n len index data) y)))
  :hints (("Goal" :in-theory (enable bv-array-read natp))))

(defthm bvplus-of-bv-array-read-arg2
  (implies (and (< n element-size)
                (natp n)
                (integerp element-size))
           (equal (bvplus n x (bv-array-read element-size len index data))
                  (bvplus n x (bv-array-read n len index data))))
  :hints (("Goal" :in-theory (enable bv-array-read natp))))

;hack for rc2..
(defthmd bvuminus-of-bv-array-read
  (implies (and (< n element-size)
                (natp n)
                (integerp element-size))
           (equal (bvuminus n (bv-array-read element-size len index data))
                  (bvuminus n (bv-array-read n len index data))))
  :hints (("Goal" :in-theory (enable bv-array-read natp))))

;is this strictly better?
(defthm take-of-bv-array-write-better
  (implies (and (<= n len)
                (< key len) ;Mon Jul 19 20:51:44 2010
                (natp n)
                (natp len)
                (natp key))
           (equal (take n (bv-array-write element-size len key val lst))
                  (if (< key n)
                      (bv-array-write element-size n key val (take n lst))
                    (bvchop-list element-size (take n lst)))))
  :hints (("Goal" :in-theory (e/d (update-nth2 bv-array-write-opener)
                                  (update-nth-becomes-update-nth2-extend-gen)))))

;todo -add hyps
;Thu Mar  4 15:41:42 2010
;; (skip -proofs
;; (defthmd update-nth2-becomes-bv-array-write-8
;;    (implies (and (all-unsigned-byte-p 8 lst)
;;                  (unsigned-byte-p 8 val))
;;             (equal (update-nth2 len key val lst)
;;                    (bv-array-write 8
;;                                   len
;;                                   key
;;                                   val
;;                                   lst)))))


(defthmd update-nth2-becomes-bv-array-write32
  (implies (and (all-unsigned-byte-p 32 lst)
                (unsigned-byte-p 32 val)
                ;;new:
                (< key len)
                (natp key)
                (true-listp lst)
                (equal len (len lst))
                )
           (equal (update-nth2 len key val lst)
                  (bv-array-write 32
                                  len
                                  key
                                  val
                                  lst)))
  :hints (("Goal" :in-theory (e/d (bv-array-write-opener UPDATE-NTH2) (UPDATE-NTH-BECOMES-UPDATE-NTH2-EXTEND-GEN)))))

;special case for bv-array-write:
;move
(defthm bv-array-read-of-bv-array-write-shorten
  (implies (and (syntaxp (and (quotep len2)
                              (quotep len1)))
                (< len1 len2)
                (< index1 len1) ;Mon Jul 19 20:52:24 2010
                (< index2 len2) ;Mon Jul 19 20:52:24 2010
                (< index2 len1) ;Mon Jul 19 20:52:24 2010
                (NOT (< (LEN DATA) LEN1)) ;Mon Jul 19 20:54:37 2010
                (EQUAL (LEN DATA) LEN2) ;Mon Jul 19 20:54:37 2010
                (natp len2) ;(integerp len2)
                (natp index2)  ;Mon Jul 19 20:54:37 2010
                (posp len1))
           (equal (bv-array-read element-size len1 index1 (bv-array-write element-size len2 index2 val data))
                  (bv-array-read element-size len1 index1 (bv-array-write element-size len1 index2 val data))))
  :hints (("Goal" :use (:instance bv-array-read-shorten-data (len len1) (index index1) (data (bv-array-write element-size len2 index2 val data)))
           :in-theory (disable bv-array-read-shorten-data
                               bv-array-write ;fixme
                               ;BV-ARRAY-READ-OF-TAKE
                               ;FIRSTN-BECOMES-TAKE-GEN
                               ))))

(DEFTHM bv-array-read-OF-UPDATE-SUBRANGE2
  (IMPLIES (AND (NATP START)
                (NATP END)
                (<= (+ -1 START) END)
                (< END LEN)
                (NATP N)
                (< N LEN)
                (NATP LEN))
           (EQUAL (bv-array-read width len N (UPDATE-SUBRANGE2 LEN START END VALS LST))
                  (IF (< N START)
                      (bv-array-read width len N LST)
                      (IF (< END N)
                          (bv-array-read width len N LST)
                          (bv-array-read width (+ 1 end (- start)) (- N START) VALS)))))
  :HINTS (("Goal" :IN-THEORY (E/d (bv-array-read-OPENER natp)
                                  (;NTH-BECOMES-BV-ARRAY-READ-NON-DAG
                                   )))))


;dup
(defthmd getbit-of-bv-array-read-helper
  (implies (and (natp n)
                (< n element-size)
                (posp len)
                (natp element-size))
           (equal (getbit n (bv-array-read element-size len index data))
                  (bv-array-read 1 len index (getbit-list n data))))
  :hints (("Goal" :in-theory (enable getbit-list
                                     natp posp bv-array-read GETBIT-WHEN-VAL-IS-NOT-AN-INTEGER BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))))

(defthmd bv-array-read-blast-helper
  (implies (and (< 1 element-width)
                (posp len)
                (integerp element-width))
           (equal (bv-array-read element-width len index data)
                  (bvcat 1
                         (bv-array-read 1 len index (getbit-list (+ -1 element-width) data))
                         (+ -1 element-width)
                         ;wrap a bvchop-list around the data?
                         (bv-array-read (+ -1 element-width) len index data))))
  :hints (("Goal" :in-theory (enable GETBIT-OF-BV-ARRAY-READ-HELPER bvchop-of-bv-array-read
                                     slice-becomes-getbit))))

;what should we do when the data is not a quotep?
(defthmd bv-array-read-blast
  (implies (and (syntaxp (quotep data))
                (< 1 element-width)
                (posp len)
                (integerp element-width))
           (equal (bv-array-read element-width len index data)
                  (bvcat 1
                         (bv-array-read 1 len index (getbit-list (+ -1 element-width) data))
                         (+ -1 element-width)
                         ;wrap a bvchop-list around the data?
                         (bv-array-read (+ -1 element-width) len index data))))
  :hints (("Goal" :use (:instance bv-array-read-blast-helper))))

;or just use NTH-OF-UPDATE-SUBRANGE2?
;fixme improve? only one of lst and vals (the one from which the value selected) needs to be a usb-list?
(defthm unsigned-byte-p-of-nth-of-update-subrange2
  (implies (and (natp n)
                (< n len) ;move to conclusion?
                (<= len (len lst))
                (<= (+ 1 (- end start)) (len vals))
                (natp start)
                (natp end)
                (natp len)
                (all-unsigned-byte-p width lst)
                (all-unsigned-byte-p width vals))
           (unsigned-byte-p width (nth n (update-subrange2 len start end vals lst))))
  :hints (("Goal" :in-theory (enable ;LIST::NTH-APPEND
                              ))))



;has the right len for the read in the rhs
;move
(DEFTHM BV-ARRAY-READ-OF-SUBRANGE-better
  (IMPLIES
   (AND (NATP INDEX)
        (NATP START)
        (<= START END)
        (INTEGERP END)
        (< INDEX LEN)
        (EQUAL LEN (+ END 1 (- START)))
        (< END (LEN LST))
        (NATP ELEMENT-SIZE))
   (EQUAL (BV-ARRAY-READ ELEMENT-SIZE
                         LEN INDEX (SUBRANGE START END LST))
          (BV-ARRAY-READ ELEMENT-SIZE (len lst) ;(+ 1 END)
                         (+ START INDEX)
                         LST)))
  :hints (("Goal" :in-theory (enable bv-array-read-opener bvchop-when-i-is-not-an-integer))))
