; Mixed rules 1
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

;; These are mostly about lists and arrays of BVs

;;  This file was called axerulescore.lisp.

(include-book "list-rules")
(include-book "kestrel/bv-lists/list-patterns" :dir :system) ;for negated-elems-listp
(include-book "kestrel/bv/unsigned-byte-p" :dir :system)
(include-book "kestrel/bv/bvcat" :dir :system)
(include-book "kestrel/bv/rules" :dir :system)
(include-book "kestrel/bv-lists/bvnth" :dir :system)
(include-book "kestrel/bv-lists/bytes-to-bits" :dir :system)
(local (include-book "kestrel/bv-lists/bytes-to-bits2" :dir :system))
(include-book "kestrel/bv-lists/bv-arrays" :dir :system)
(include-book "kestrel/typed-lists-light/integer-lists" :dir :system) ;for ALL-INTEGERP-WHEN-ALL-NATP
(include-book "kestrel/bv-lists/all-signed-byte-p" :dir :system) ;todo
(include-book "kestrel/bv-lists/getbit-list" :dir :system)
(include-book "axe-syntax") ;for work-hard -- TODO make non-work-hard versions of these..  could make a macro to copy a theorem and wrap work-hard around a hyp..
(include-book "kestrel/lists-light/update-subrange" :dir :system)
(include-book "kestrel/lists-light/update-subrange2" :dir :system)
(local (include-book "kestrel/library-wrappers/arithmetic-inequalities" :dir :system)) ;todo
(local (include-book "kestrel/bv-lists/all-unsigned-byte-p2" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/less-than" :dir :system))
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


;expensive?
;fixme which do we prefer?  depends on priorities..
;not needed except for axe?
;rename
(defthmd len-equal-0-rewrite-alt
  (equal (equal (len x) 0)
         (not (consp x))))

;move
(defthm nthcdr-of-len-same-when-true-listp
  (implies (true-listp x)
           (equal (nthcdr (len x) x)
                  nil)))

;TTODO: Move these rules to the appropriate libraries!
;TODO: Handle the things with -dag in the name

(local (in-theory (enable BVCHOP-WHEN-I-IS-NOT-AN-INTEGER)))

(local (in-theory (disable NATP-WHEN-UNSIGNED-BYTE-P-SIZE-ARG)))

;(local (in-theory (disable LIST::FIX-OF-NTHCDR))) ;loops with NTHCDR-OF-TRUE-LIST-FIX !

;think about how to say this...
;; (defthm if-rule4
;;   (iff (if x x t) ;helps with ors?
;;          x)
;;   :rule-classes nil)

;gets rid of extra bits in the bvcat indices - without this, we may have had big problems...
;bozo gen?
(defthm bvnth-of-bvcat-8-case
  (implies (and (< 8 (+ n lowsize))
                (natp lowsize)
                (natp n)
;                (natp esize)
;                (equal 8 esize) ;bozo
                )
           (equal (bvnth esize 8 (bvcat n highval lowsize lowval) data)
                  (if (<= 8 lowsize)
                      (bvnth esize 8 lowval data)
                    (bvnth esize 8 (bvcat (- 8 lowsize) highval lowsize lowval) data))))
  :hints (("Goal" :in-theory (enable bvnth))))

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
;;                             ) ( BVPLUS-RECOLLAPSE BVMULT-OF-BVCHOP-arg3)))))

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
;;   :hints (("Goal" :in-theory (e/d (bvplus) (anti-bvplus)))))

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



(defthmd nth-of-slice-becomes-nth2
  (implies (and (natp high)
                (natp low)
                (<= low high))
           (equal (nth (slice high low index)  lst)
                  (nth2 (+ 1 high (- low)) (slice high low index) lst)))
  :hints (("Goal" :in-theory (enable nth2))))

(defthmd nth-of-bvchop-becomes-nth2
  (equal (nth (bvchop size index)  lst)
         (nth2 size (bvchop size index) lst))
  :hints (("Goal" :in-theory (enable nth2))))

(defthmd nth-of-bvxor-becomes-nth2
  (implies (and (natp size))
           (equal (nth (bvxor size x y)  lst)
                  (nth2 size (bvxor size x y) lst)))
  :hints (("Goal" :in-theory (enable nth2))))

(defthm nth-of-bvcat-becomes-nth2
  (implies (and (natp highsize)
                (natp lowsize)
                (<= lowsize highsize))
           (equal (nth (bvcat highsize highval lowsize lowval)  lst)
                  (nth2 (+ highsize lowsize) (bvcat highsize highval lowsize lowval) lst)))
  :hints (("Goal" :in-theory (enable nth2))))

(defthm nth2-becomes-bvnth-for-natps
  (implies (and (all-natp vals)
                (natp indexsize)
                (natp index)
                (< index (len vals))
                )
           (equal (nth2 indexsize index vals)
                  (bvnth (width-of-widest-int vals)
                         indexsize
                         index
                         vals)))
  :hints (("Goal"
           :cases ((<= (bvchop indexsize index) index))
           :in-theory (enable nth2 bvnth ;all-integerp-when-all-natp
                              ))))

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
;;   :otf-flg t
;;   :hints (("Goal" ;:cases ((natp index) (not (integerp index)))
;;            :in-theory (enable bvnth all-integerp-when-all-natp nth2
;;                               BVCHOP-WHEN-I-IS-NOT-AN-INTEGER
;;                                      ADD-BVCHOPS-TO-EQUALITY-OF-SBPS-4-ALT))))

(defthm getbit-of-bvnth-too-high
  (implies (and (<= size n)
                (natp n)
                (natp size))
           (equal (getbit n (bvnth size isize index vals))
                  0))
  :hints (("Goal" :in-theory (enable getbit-too-high))))

;BOZO we want to use update-nth2 for arrays, but not for locals (which shouldn't blow up, since we should always be able to resolve nths into the locals...)

;BOZO build update-nth2 into the machine model?
;newly disabled..
(defthmd update-nth-becomes-update-nth2
  (implies (and (true-listp lst)
                (< key (len lst))
                (natp key))
           (equal (update-nth key val lst)
                  (update-nth2 (len lst)
                               key
                               val lst)))
  :hints (("Goal" :in-theory (enable update-nth2))))

(DEFTHMd NTH2-BECOMES-BVNTH-8
  (IMPLIES (AND (all-unsigned-byte-p 8 vals)
                ;;(ALL-NATP VALS)
                (NATP INDEXSIZE)
                (NATP INDEX)
                (< INDEX (LEN VALS)))
           (EQUAL (NTH2 INDEXSIZE INDEX VALS)
                  (BVNTH 8 INDEXSIZE INDEX VALS)))
  :HINTS
  (("Goal"
    :CASES ((<= (BVCHOP INDEXSIZE INDEX) INDEX))
    :IN-THEORY (E/d (NTH2 BVNTH
                          ALL-INTEGERP-WHEN-ALL-NATP) (NTH-OF-BVCHOP-BECOMES-NTH2)))))

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
;;                                                 CDR-OF-TAKE-BECOMES-SUBRANGE-BETTER
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

(DEFTHMd NTH2-BECOMES-BVNTH-32
  (IMPLIES (AND (all-unsigned-byte-p 32 vals)
                ;(ALL-NATP VALS)
                (NATP INDEXSIZE)
                (NATP INDEX)
                (< INDEX (LEN VALS)))
           (EQUAL (NTH2 INDEXSIZE INDEX VALS)
                  (BVNTH 32 INDEXSIZE INDEX VALS)))
  :HINTS
  (("Goal"
    :CASES ((<= (BVCHOP INDEXSIZE INDEX) INDEX))
    :IN-THEORY (E/d (NTH2 BVNTH
                       ALL-INTEGERP-WHEN-ALL-NATP) (NTH-OF-BVCHOP-BECOMES-NTH2)))))

;bbozo gross
(defthm bvnth-tighten-32-8
  (implies (all-unsigned-byte-p 8 data)
           (equal (bvnth 32 index-size index data)
                  (bvnth 8 index-size index data)))
  :hints (("Goal" :cases ((< (BVCHOP INDEX-SIZE INDEX) (LEN DATA)))
           :in-theory (enable bvnth slice-too-high-is-0
                              ;;LIST::NTH-WITH-LARGE-INDEX
                              ))))

;BOZO classify these rules somehow (separate the ones for the symbolic simulation?)

;BOZO yuck!
;newly disabled
(defthmd not-<-self2
  (implies (equal x y)
           (not (< x y))))

;just a special case of a cancellation rule
(defthm <-of-+-of-1-same
  (< x (+ 1 x)))

;just a special case of a cancellation rule
(defthm <-of-+-of-1-same-alt
  (not (< (+ 1 x) x)))

;should collect the constants
;could then use a rule that len is not equal to an impossible constant
(defthm one-plus-len-hack
  (equal (equal (+ 1 (len x)) 0)
         nil))



;BBOZO what do we currently do with free variables?

(defthm hack-arith-cancel
  (equal (< (+ a x) (+ b x))
         (< a b)))

;maybe this won't happen for arrays, since they start out initialized to their final length?
(defthm update-nth-becomes-update-nth2-extend
  (implies (and (true-listp lst)
                (equal key (len lst))
                (natp key))
           (equal (update-nth key val lst)
                  (update-nth2 (+ 1 (len lst))
                               key
                               val lst)))
  :hints (("Goal" :in-theory (enable update-nth2))))

(in-theory (disable update-nth-becomes-update-nth2 update-nth-becomes-update-nth2-extend))

;move
(defthm update-nth-of-take-of-+-of-1-same
  (implies (and (<= (len lst) n)
                (natp n))
           (equal (update-nth n val (take (+ 1 n) lst))
                  (update-nth n val lst)))
  :hints (("Goal" :in-theory (enable update-nth))))

(defthmd update-nth-becomes-update-nth2-extend-gen
  (implies (and (true-listp lst)
                (>= key (len lst))
                (natp key))
           (equal (update-nth key val lst)
                  (update-nth2 (+ 1 key)
                               key
                               val
                               lst)))
  :hints (("Goal" :in-theory (enable update-nth2 ;LIST::LEN-UPDATE-NTH-BETTER
                                     equal-of-append))))



;drop? expensive?
(DEFTHMD USBP8-IMPLIES-SBP32-2
  (IMPLIES (UNSIGNED-BYTE-P 8 X)
           (equal (SIGNED-BYTE-P 32 X)
                  t)))

(defthm natp-means-non-neg
  (implies (natp n)
           (not (< n 0))))

(defthmd update-nth2-of-update-nth2-diff
  (implies (and (syntaxp (quotep i1))
                (syntaxp (quotep i2))
                (< i1 len)
                (< i2 i1)
                (natp i1)
                (natp i2)
                (natp len)
                (true-listp l)
                (equal len (len l))
                )
           (equal (update-nth2 len i1 v1 (update-nth2 len i2 v2 l))
                  (update-nth2 len i2 v2 (update-nth2 len i1 v1 l))))
  :hints (("Goal"
           :in-theory (enable update-nth2 ;LIST::UPDATE-NTH-UPDATE-NTH-DIFF
                              ))))

(defthm update-nth2-of-update-nth2-same
  (implies (and (< i len)
                (natp i)
                (natp len)
                )
           (equal (update-nth2 len i v1 (update-nth2 len i v2 l))
                  (update-nth2 len i v1 l)))
  :hints (("Goal"
           :in-theory (enable update-nth2 ;LIST::UPDATE-NTH-UPDATE-NTH-DIFF
                              ))))

;use iff?
;drop this one?
(defthm subrange-not-nil1
  (implies (and ;(consp lst)
                (natp start)
                (natp end))
           (equal (equal (subrange start end lst) nil)
                  (< end start)
                  ))
  :hints (("Goal" :in-theory (e/d (subrange) (;anti-subrange
                                              )))))

;use iff?
(defthm subrange-not-nil2
  (implies (and ;(consp lst)
                (natp start)
                (natp end))
           (equal (equal nil (subrange start end lst))
                  (< end start)
                  ))
  :hints (("Goal" :use (:instance subrange-not-nil1)
           :in-theory (disable subrange-not-nil1))))

;; ;fixme the same as append-of-cons?
;; (DEFTHM LIST::xAPPEND-OF-CONS-BETTER2
;; ;  (IMPLIES (SYNTAXP (NOT (AND (QUOTEP X) (QUOTEP A))))
;;            (EQUAL (APPEND (CONS A X) Y)
;;                   (CONS A (APPEND X Y)))
;;            ;)
;;   :HINTS
;;   (("Goal" :IN-THEORY (DISABLE LIST::EQUAL-APPEND-REDUCTION!))))

;todo: bad name
(defthm update-nth-becomes-update-nth2-extend-new
  (implies (and (true-listp lst)
                (equal key (len lst))
                (natp key))
           (equal (update-nth key val lst)
                  (append lst (list val))))
  :hints (("Goal" :in-theory (e/d (update-nth2) (update-nth-becomes-update-nth2 update-nth-becomes-update-nth2-extend UPDATE-NTH-BECOMES-UPDATE-NTH2-EXTEND-GEN)))))

;; (DEFTHM UPDATE-NTH2-OF-CONS
;;   (EQUAL (UPDATE-NTH2 len N VAL (CONS A LST))
;;          (IF (ZP N)
;;              (CONS VAL LST)
;;              (CONS A (UPDATE-NTH (+ -1 N) VAL LST)))))

;bozo some dups above this?

;for axe
(defthmd if-of-if-t-nil
  (equal (if (if test t nil) foo bar)
         (if test foo bar)))

;TODO: do we still use bvnth?
;move?
(defthm bvnth-becomes-bv-array-read
  (implies (and (natp index-size)
                ;; (< index (expt 2 index-size))
                ;; (natp index)
                )
           (equal (bvnth element-size index-size index data)
                  (bv-array-read element-size (expt 2 index-size) (bvchop index-size index) data)))
  :otf-flg t
  :hints (("Goal" :in-theory (enable bv-array-read bvnth ceiling-of-lg))))




;=== stuff to support array-reduction-when-top-bit-is-xored-in

;bozo may be slow?
;; (defthm bit-listp-implies-all-integerp
;;   (implies (all-unsigned-byte-p 1 vals)
;;            (all-integerp vals))
;;   :hints (("Goal" :in-theory (enable all-integerp))))

(defthmd nth-sum-when-nthcdr-known
  (implies (and (EQUAL vals2 (NTHCDR m VALS))
                (natp n)
                (natp m))
           (equal (NTH (+ m n) VALS)
                  (NTH n VALS2)
                  )))

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
  :otf-flg t
  :hints (("Goal" :expand ((BVNOT-LIST ELEM-SIZE (TAKE (EXPT 2 N) VALS))
                           (NTHCDR (EXPT 2 N) VALS))
           :in-theory (disable NTHCDR-OF-CDR-COMBINE-STRONG NTHCDR-OF-CDR-COMBINE)
           )))

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
  :otf-flg t
  :hints (("Goal"
           :cases ((equal 0 (getbit 0 x)))
           :use (:instance gross-hack)
           :in-theory (e/d (bvplus ;-opener
                            nth-sum-when-nthcdr-known
                            bvcat-special-opener
                            bv-array-read ceiling-of-lg
;                                        car-of-both-sides-alt
;                                       car-of-both-sides
                            ;bvplus-recollapse
                            EXPONENTS-ADD-FOR-NONNEG-EXPONENTS
                            subrange
                            )
                           (gross-hack
                            nth-of-cdr
                            ;NTH-SUM-WHEN-NTHCDR-KNOWN
                            NTH-OF-NTHCDR ;looped
                            ;NTH-SUM-WHEN-NTHCDR-KNOWN
;NTH-SUM-WHEN-NTHCDR-KNOWN
                            REPEATBIT-OF-1-ARG2
;NTH-SUM-WHEN-NTHCDR-KNOWN
                            NTHCDR-OF-CDR-COMBINE-STRONG NTHCDR-OF-CDR-COMBINE
;(:REWRITE NTH-SUM-WHEN-NTHCDR-KNOWN) ;
                            ;LIST::NTH-NTHCDR
                            NTH-OF-TAKE-GEN
;NTH-OF-BVNOT-LIST
;BV-ARRAY-READ-OF-TAKE
;BV-ARRAY-READ-OF-BVCHOP
;BV-ARRAY-READ-OF-BVCHOP-HELPER
                            )))))

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
  :hints (("Goal" :in-theory (enable subrange)
           :use (:instance array-reduction-when-top-bit-is-xored-in-helper-helper
                           (x (getbit n index))
                           (y (bvchop n index))
                           (vals (true-list-fix vals))))))

(defthmd even-when-power-of-2-and-at-least-2
  (implies (and (<= 2 n)
                (power-of-2p n))
           (integerp (binary-* 1/2 n)))
  :hints (("Goal" :in-theory (e/d (expt-collect-hack natp) (exponents-add)))))

(defthm equal-of-nthcdr-and-subrange-of-minus1
  (implies (and (natp n)
                (natp len)
                (<= len (len array))
                (true-listp array)
                (<= n len)
                )
           (equal (equal (nthcdr n array) (subrange n (+ -1 len) array))
                  (equal len (len array))))
  :hints (("Goal" :in-theory (e/d (subrange) (;take-of-nthcdr-becomes-subrange
                                              ;nthcdr-of-take-becomes-subrange
                                              ;;cdr-of-take-becomes-subrange-better
                                              )))))


(defthm +-of-half
  (equal (+ len (- (* 1/2 len)))
         (* 1/2 len)))

(defthm firstn-of-bvchop-list
  (equal (firstn n (bvchop-list size array))
         (bvchop-list size (firstn n array)))
  :hints (("Goal" :in-theory (enable bvchop-list firstn))))

(local (in-theory (disable NTH-SUM-WHEN-NTHCDR-KNOWN))) ;looped

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
;;                        (nthcdr (/ len 2) array) ;;slow: (subrange (/ len 2) (+ -1 len) array) ;ffixme this could just be an nthdr?
;;                        )
                (natp elem-size))
           (equal (bv-array-read elem-size len index array)
                  (bvxor elem-size
                         (repeatbit elem-size (getbit (+ -1 (lg len)) index))
                         (bv-array-read elem-size
                                        (/ len 2)
                                        (bvchop (+ -1 (lg len)) index)
                                        (firstn (/ len 2) array)))))
  :otf-flg t
  :hints (("Goal"
           :in-theory (e/d (power-of-2p expt-of-+ natp even-when-power-of-2-and-at-least-2 lg
                                        SUBRANGE ;prove an nthdr=subrange rule
                                        )
                           (array-reduction-when-top-bit-is-xored-in-helper ;TAKE-WHEN-<-OF-LEN
                                                                            ;TAKE-OF-NTHCDR-BECOMES-SUBRANGE
                                                                            ;NTHCDR-OF-TAKE-BECOMES-SUBRANGE
                                                                            ;CDR-OF-TAKE-BECOMES-SUBRANGE-BETTER
                                                                            ))
           :use (:instance array-reduction-when-top-bit-is-xored-in-helper
                           (vals (bvchop-list elem-size (take len (true-list-fix array))))
                           (n (+ -2 (integer-length len)))))))

(defthm array-reduction-when-top-bit-is-irrelevant-helper
  (implies (and ;(integerp y)
;(<= 0 y)
            (natp n)
            (equal (len vals) (expt 2 (+ 1 n)))
            (true-listp vals)
            (all-unsigned-byte-p 1 vals)
            (equal (firstn (expt 2 n) vals)
                   (subrange (expt 2 n) (+ -1 (expt 2 n) (expt 2 n)) vals))
            )
           (equal (bv-array-read 1 (expt 2 (+ 1 n)) (bvcat 1 x n y) vals)
                  (bv-array-read 1 (expt 2 n) (bvchop n y) (firstn (expt 2 n) vals))))
  :otf-flg t
  :hints (("Goal"
           :cases ((equal 0 (getbit 0 x)))
           :in-theory (e/d (nth-sum-when-nthcdr-known bvcat-special-opener bv-array-read ceiling-of-lg subrange)
                           (NTH-OF-NTHCDR
                            BV-ARRAY-READ-OF-BVCHOP-HELPER
                            BV-ARRAY-READ-OF-BVCHOP
                            BV-ARRAY-READ-OF-TAKE
;list::nth-nthcdr
                            )))))

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
;;  :hints (("Goal" :in-theory (e/d (getbit) (SLICE-BECOMES-GETBIT BVCHOP-1-BECOMES-GETBIT)))))

;drop the getbit?
(defthm array-reduction-1-0
  (equal (bv-array-read 1 2 index '(1 0))
         (bitnot (getbit 0 (ifix index))))
;  :otf-flg t
  :hints (("Goal"
           :expand (NTH (GETBIT 0 INDEX) '(1 0))
           :in-theory (e/d (bitnot bv-array-read ;LIST::NTH-OF-CONS
                                   GETBIT-WHEN-VAL-IS-NOT-AN-INTEGER
                                   )
                           ()))))

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

;add to forall
(defthm all-signed-byte-p-of-nil
  (equal (all-signed-byte-p n nil)
         t)
  :hints (("Goal" :in-theory (enable all-signed-byte-p))))

(DEFTHM SIGNED-BYTE-P-OF-MYIF2
  (IMPLIES (AND (SIGNED-BYTE-P N A)
                (SIGNED-BYTE-P N B))
           (equal (SIGNED-BYTE-P N (MYIF TEST A B))
                  t))
  :HINTS (("Goal" :IN-THEORY (ENABLE MYIF))))

;keep but move
;; (defthm all-signed-byte-p-of-logext-list
;;   (implies (and (integerp size)
;;                 (< 0 size))
;;            (equal (all-signed-byte-p size (logext-list size lst))
;;                   t))
;;   :hints (("Goal" :in-theory (enable logext-list all-signed-byte-p))))

(DEFTHM all-signed-byte-p-OF-MYIF
  (IMPLIES (AND (all-signed-byte-p N A)
                (all-signed-byte-p N B))
           (equal (all-signed-byte-p N (MYIF TEST A B))
                  t))
  :HINTS (("Goal" :IN-THEORY (ENABLE MYIF))))

(DEFTHM all-signed-byte-p-OF-MYIF-strong
  (equal (all-signed-byte-p N (MYIF TEST A B))
         (myif test (all-signed-byte-p N A)
               (all-signed-byte-p N B)))
  :HINTS (("Goal" :IN-THEORY (ENABLE MYIF))))

(DEFTHM all-unsigned-byte-p-OF-MYIF-strong
  (equal (all-unsigned-byte-p N (MYIF TEST A B))
         (myif test (all-unsigned-byte-p N A)
               (all-unsigned-byte-p N B)))
  :HINTS (("Goal" :IN-THEORY (ENABLE MYIF))))

(defthm all-signed-byte-p-of-update-nth
  (implies (and (signed-byte-p m val)
                (natp m)
                (<= n (len lst))
                (all-signed-byte-p m lst))
           (all-signed-byte-p m (update-nth n val lst)))
  :hints (("Goal" :in-theory (enable update-nth all-signed-byte-p))))

(defthm all-signed-byte-p-when-all-unsigned-byte-p
  (implies (and (all-unsigned-byte-p n x)
                (natp n)
                (< 0 n))
           (equal (all-signed-byte-p n x)
                  (all-unsigned-byte-p (+ -1 n) x)))
  :hints (("Goal" :in-theory (e/d (all-signed-byte-p all-unsigned-byte-p)
                                  ()))))

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

;(local (in-theory (disable BVPLUS-RECOLLAPSE)))

(DEFTHM ALL-UNSIGNED-BYTE-P-OF-BVCHOP-LIST-GEN2
  (IMPLIES (AND ;(<= ELEMENT-SIZE SIZE)
            (ALL-UNSIGNED-BYTE-P SIZE LST)
            (NATP SIZE)
            (NATP ELEMENT-SIZE))
           (EQUAL (ALL-UNSIGNED-BYTE-P SIZE (BVCHOP-LIST ELEMENT-SIZE LST))
                  T))
  :HINTS
  (("Goal"
    :IN-THEORY (ENABLE ALL-UNSIGNED-BYTE-P BVCHOP-LIST))))

(defthmd logext-bound-when-unsigned-byte-p
  (implies (and (syntaxp (quotep k))
                (< 0 k)
                (natp k)
                (<= k (expt 2 (+ -1 n)))
                (< x k)
                (unsigned-byte-p n x)
                (natp n)
                (< 0 n)
                )
           (< (logext n x) k))
  :hints (("Goal" :in-theory (enable ;logext
                              ))))


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
(defthm bv-array-read-of-logext-64-32
  (implies (and ; (unsigned-byte-p 32 x)
;               (<= 0 (logext 32 x))
            (integerp x)
            (integerp m)
            (<= 6 m)
            )
           (equal (bv-array-read n 64 (logext m x) vals)
                  (bv-array-read n 64 (bvchop 6 x) vals)))
  :hints (("Goal" :in-theory (enable bv-array-read BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))))

(defthm equal-of-repeat-of-len-same
  (equal (equal data (repeat (len data) item))
         (and (true-listp data)
              (all-equal$ item data))))

;bozo should we restrict this to constant arrays?
(DEFTHM ARRAY-REDUCTION-WHEN-ALL-SAME-improved
  (IMPLIES (AND (all-equal$ (car data) data) ;old way (involves consing): (EQUAL DATA (REPEAT (LEN DATA) (CAR DATA)))
                (NATP INDEX)
                (< INDEX LEN)
                (EQUAL (LEN DATA) LEN)
                (TRUE-LISTP DATA)
                (ALL-UNSIGNED-BYTE-P ELEMENT-SIZE DATA))
           (EQUAL (BV-ARRAY-READ ELEMENT-SIZE LEN INDEX DATA)
                  (BV-ARRAY-READ ELEMENT-SIZE LEN 0 DATA) ;(BVCHOP ELEMENT-SIZE (CAR DATA))
                  ))
  :hints (("Goal" :use (:instance ARRAY-REDUCTION-WHEN-ALL-SAME)
           :in-theory (disable ARRAY-REDUCTION-WHEN-ALL-SAME; CAR-BECOMES-NTH-OF-0
                               ))))

;; This could loop when INDEX is the constant 0, except that then the whole
;; bv-array-read should be evaluated because all the args would be constants.
(defthmd array-reduction-when-all-same-improved2
  (implies (and (syntaxp (quotep data))
                (syntaxp (quotep len)) ;these prevent loops
                (syntaxp (quotep element-size))
                ;; should be evaluated:
                (all-equal$ (bv-array-read element-size len 0 data) data) ;old way (involves consing): (equal data (repeat (len data) (car data)))
                (natp index)
                (< index len)
                (equal (len data) len)
                (true-listp data)
                (all-unsigned-byte-p element-size data))
           (equal (bv-array-read element-size len index data)
                  (bv-array-read element-size len 0 data) ;(bvchop element-size (car data))
                  ))
  :hints (("Goal" :use (:instance array-reduction-when-all-same)
           :in-theory (e/d (;all-equal$-when-true-listp
                            )
                           ( array-reduction-when-all-same ;car-becomes-nth-of-0
                             )))))

;; This is now a legal rewrite rule.
(defthmd if-becomes-myif
  (equal (if x y z)
         (myif x y z))
  :hints (("Goal" :in-theory (enable myif))))


;is this inefficient?
(defthm true-listp-of-myif-strong
  (equal (true-listp (myif test a b))
         (myif test (true-listp a)
               (true-listp b)))
  :hints (("Goal" :in-theory (enable myif))))

(defthm true-listp-of-myif
  (implies (and (true-listp a)
                (true-listp b))
           (equal (true-listp (myif test a b))
                  t))
  :hints (("Goal" :in-theory (enable myif))))



;move
;; (defthm getbit-list-of-logext-list
;;   (implies (and (< n size)
;;                 (natp size)
;;                 (natp n))
;;            (equal (getbit-list n (logext-list size lst))
;;                   (getbit-list n lst)))
;;   :hints (("Goal" :in-theory (enable getbit-list logext-list))))

;use a trim rule!
(DEFthm BV-ARRAY-WRITE-of-bvcat-reduce
  (implies (and (<= element-size lowsize)
                (natp element-size)
                (natp highsize)
                (natp lowsize)
                (equal len (len lst))
                (< key len)
                (natp key)
                )
           (equal (BV-ARRAY-WRITE ELEMENT-SIZE LEN KEY (bvcat highsize highval lowsize lowval) LST)
                  (BV-ARRAY-WRITE ELEMENT-SIZE LEN KEY lowval LST)))
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
    :in-theory (e/d (bv-array-read bvnth GETBIT-WHEN-VAL-IS-NOT-AN-INTEGER ;NTH-WHEN-N-IS-ZP
                                   )
                    (nth-of-cdr CAR-BECOMES-NTH-OF-0)))))

;bozo now delete some rules with constants as arg2 - same thing for bvmult and other binary functions?

(local (in-theory (enable myif)))

(defthm bytes-to-bits-of-bv-array-write
  (implies (and (equal len (len lst))
                (< n len)
                (true-listp lst)
                (natp n)
                )
           (equal (bytes-to-bits (bv-array-write 8 len n val lst))
                  (append (bytes-to-bits (take n lst))
                          (list (getbit 7 val)
                                (getbit 6 val)
                                (getbit 5 val)
                                (getbit 4 val)
                                (getbit 3 val)
                                (getbit 2 val)
                                (getbit 1 val)
                                (getbit 0 val))
                          (bytes-to-bits (nthcdr (+ 1 n) lst))
                          )))
  :hints (("Goal"
           :expand (BYTES-TO-BITS (UPDATE-NTH 0 VAL (NTHCDR N LST)))
           :in-theory (enable bytes-to-bits byte-to-bits update-nth2 bv-array-write ceiling-of-lg equal-of-append CDR-OF-NTHCDR))))

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
                                  (;BVPLUS-RECOLLAPSE
                                   unsigned-byte-p-of-+-of-minus-alt
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


;not true for negative vals!
(defthm nth-of-bvcat-becomes-bvnth-for-natps
  (implies (and (all-natp vals)
                (natp HIGHSIZE)
                (natp lowsize)
                (< (bvcat highsize highval lowsize lowval) (len vals))
                )
           (equal (nth (bvcat highsize highval lowsize lowval) vals)
                  (bvnth (width-of-widest-int vals)
                         (+ highsize lowsize)
                         (bvcat highsize highval lowsize lowval)
                         vals)))
  :hints (("Goal" :in-theory (enable bvnth all-integerp-when-all-natp))))

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
;;   :otf-flg t
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
  :otf-flg t
  :hints (("Goal"
           :cases ((and (equal 1 (getbit 0 a)) (equal 1 (getbit 0 b)))
                   (and (not (equal 1 (getbit 0 a))) (equal 1 (getbit 0 b)))
                   (and (equal 1 (getbit 0 a)) (not (equal 1 (getbit 0 b)))))
           :in-theory (e/d () ( ;GETBIT-WHEN-NOT-0
;GETBIT-WHEN-NOT-1
                               NTH-OF-BVCAT-BECOMES-NTH2
                               )))))

(defthmd nth-of-if-arg2
  (equal (nth n (if test a b))
         (if test (nth n a) (nth n b))))


;; (defthm myif-of-logext-list-and-logext-list
;;   (equal (myif test (logext-list n x) (logext-list n y))
;;          (logext-list n (myif test x y)))
;;   :hints (("Goal" :in-theory (enable myif))))

;ffixme use a higher order function?
(defund MAX-INTEGER-LENGTH (lst)
  (if (endp lst)
      0 ;hope this is okay
    (max (integer-length (car lst))
         (MAX-INTEGER-LENGTH (cdr lst)))))

(defthm max-integer-length-bound
  (implies (and (< n (len lst))
                (natp n))
           (<= (INTEGER-LENGTH (NTH n Lst))
               (MAX-INTEGER-LENGTH Lst)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (MAX-INTEGER-LENGTH nth) (nth-of-cdr)))))

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
;;    :otf-flg t
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
;;                              BVCHOP-OF-LOGTAIL-BECOMES-SLICE
;;                              BVCHOP-OF-LOGTAIL-BECOMES-SLICE
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


(DEFTHMd NTH-OF-BVCAT-BECOMES-BVNTH-FOR-NATPS-hack
  (IMPLIES (AND (all-unsigned-byte-p 4 vals)
                ;(ALL-NATP VALS)
                (NATP HIGHSIZE)
                (NATP LOWSIZE)
                (< (BVCAT HIGHSIZE HIGHVAL LOWSIZE LOWVAL) (LEN VALS))
                )
           (EQUAL (NTH (BVCAT HIGHSIZE HIGHVAL LOWSIZE LOWVAL) VALS)
                  (BVNTH 4
                         (+ HIGHSIZE LOWSIZE)
                         (BVCAT HIGHSIZE HIGHVAL LOWSIZE LOWVAL)
                         VALS)))
  :HINTS
  (("Goal"
    :IN-THEORY (E/d (BVNTH BV-ARRAY-READ
                       ALL-INTEGERP-WHEN-ALL-NATP) (NTH-OF-BVCAT-BECOMES-BVNTH-FOR-NATPS)))))


;how can we easily turn a nest of conses into a nest of bv-array-write calls?

;bozo
(defthmd cons-becomes-bv-array-write-size-4
  (implies (unsigned-byte-p 4 a)
           (equal (cons a nil)
                  (bv-array-write 4 1 0 a (list 0))))
  :hints (("Goal" :in-theory (enable update-nth2 bv-array-write))))

;bozo
(defthmd cons-becomes-bv-array-write-size-1
  (implies (unsigned-byte-p 1 a)
           (equal (cons a nil)
                  (bv-array-write 1 1 0 a (list 0))))
  :hints (("Goal" :in-theory (enable update-nth2 bv-array-write))))

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

(in-theory (enable nth-of-bv-array-write-becomes-bv-array-read))

(defthmd bv-array-write-tighten-to-1-bit
  (implies (and (< 1 esize)
                (all-unsigned-byte-p 1 data)
                (unsigned-byte-p 1 val)
                (NATP ESIZE)
                (equal len (len data))
                (natp index)
                (true-listp data)
                (< INDEX LEN))
           (equal (bv-array-write esize len index val data)
                  (bv-array-write 1 len index val data)))
  :hints (("Goal" :in-theory (e/d (UPDATE-NTH2 BV-ARRAY-WRITE) ()))))

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
                                  (NTH-OF-BV-ARRAY-WRITE-BECOMES-BV-ARRAY-READ
                                   ;;MYIF-OF-GETBIT-BECOMES-BVIF-ARG2 MYIF-OF-GETBIT-BECOMES-BVIF-ARG1
                                   )))))

(defthm bvif-of-bv-array-read-tighten-arg2
  (implies (and (< size1 size2)
                (natp size1)
                (natp size2))
           (equal (bvif size1 test z (bv-array-read size2 len index data))
                  (bvif size1 test z (bv-array-read size1 len index data))))
  :hints (("Goal" :in-theory (e/d (bvif myif bv-array-read)
                                  (NTH-OF-BV-ARRAY-WRITE-BECOMES-BV-ARRAY-READ
                                   ;;MYIF-OF-GETBIT-BECOMES-BVIF-ARG2 MYIF-OF-GETBIT-BECOMES-BVIF-ARG1
                                   )))))

(defthm bvchop-list-of-bvchop-list-tighten
 (implies (and (<= size1 size2)
               (natp size1)
               (natp size2))
          (equal (bvchop-list size1 (bvchop-list size2 lst))
                 (bvchop-list size1 lst)))
 :hints (("Goal" :in-theory (enable bvchop-list))))

(DEFTHMd BV-ARRAY-WRITE-OF-BV-ARRAY-WRITE-tighten
  (IMPLIES (AND (< element-size1 element-size2)
                (< INDEX1 LEN)
                (< INDEX2 LEN)
                (equal len (len lst))
                (NATP INDEX1)
                (NATP INDEX2)
                (NATP LEN)
                (NATP ELEMENT-SIZE1)
                (NATP ELEMENT-SIZE2))
           (EQUAL (BV-ARRAY-WRITE ELEMENT-SIZE1 LEN INDEX1 VAL1 (BV-ARRAY-WRITE ELEMENT-SIZE2 LEN INDEX2 VAL2 LST))
                  (BV-ARRAY-WRITE ELEMENT-SIZE1 LEN INDEX1 VAL1 (BV-ARRAY-WRITE ELEMENT-SIZE1 LEN INDEX2 VAL2 LST))))
  :hints (("Goal" :in-theory (enable update-nth2 LEN-UPDATE-NTH bv-array-write))))



(defthm nth-becomes-bvnth-when-unsigned-byte-p
  (implies (and (unsigned-byte-p size index) ;size is a free variable
                (all-natp vals)
                (<= (expt 2 size) (len vals)))
           (equal (nth index vals)
                  (bvnth (width-of-widest-int vals)
                         size
                         index
                         vals)))
  :hints (("Goal" :in-theory (enable bvnth all-integerp-when-all-natp))))



;drop?
(defthm UNSIGNED-BYTE-P-of-WIDTH-OF-WIDEST-INT-nth
  (implies (and (natp index)
                (all-natp vals)
                (< index (len vals)))
           (UNSIGNED-BYTE-P (WIDTH-OF-WIDEST-INT VALS)
                            (NTH index VALS)))
  :hints (("Goal" :in-theory (e/d (WIDTH-OF-WIDEST-INT nth) (nth-of-cdr)))))

;go get the length of the lists (using a binding hyp??)
(defthmd nth-becomes-bv-array-read
  (implies (and (syntaxp (quotep vals))
                (all-natp vals)
                (< index (len vals))
                (natp index))
           (equal (nth index vals)
                  (bv-array-read (width-of-widest-int vals) (len vals) index vals)))
  :otf-flg t
  :hints (("Goal" :in-theory (e/d (BV-ARRAY-READ bvnth all-integerp-when-all-natp ceiling-of-lg)
                                  (NTH-OF-BV-ARRAY-WRITE-BECOMES-BV-ARRAY-READ)))))

;move
(defthm nth-when-n-is-not-natp
  (implies (not (natp n))
           (equal (nth n lst)
                  (car lst)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (e/d (nth) (nth-of-cdr)))))

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
  :hints
  (("Goal" :in-theory (e/d (bv-array-read ceiling-of-lg)
                           (;list::nth-of-cons
                            NTH-OF-BV-ARRAY-WRITE-BECOMES-BV-ARRAY-READ)))))

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


(local (in-theory (enable unsigned-byte-p-forced))) ;yuck?

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
                                                   all-unsigned-byte-p-of-width-of-widest-int
                                                   nth-of-bv-array-write-becomes-bv-array-read
                                                   )))))

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
                                   NTH-OF-BV-ARRAY-WRITE-BECOMES-BV-ARRAY-READ)))))

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

(defthm bvchop-of-bvnth
  (implies (and (<= n element-size)
                (natp n)
                (natp element-size))
           (equal (bvchop n (bvnth element-size index-size index data))
                  (bvnth n index-size index data)))
  :hints (("Goal" :in-theory (enable bvnth))))

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
  :otf-flg t
  :hints (("Goal" :in-theory (e/d (bv-array-read-opener bvchop-when-i-is-not-an-integer subrange)
                                  (NTH-OF-BV-ARRAY-WRITE-BECOMES-BV-ARRAY-READ
                                   ;;BVPLUS-RECOLLAPSE
                                   )))))


;move
(defthm consp-of-myif-strong
  (equal (consp (myif test a b))
         (myif test (consp a) (consp b)))
  :hints (("Goal" :in-theory (enable myif))))

(defund push-true (fact term)
  (if fact term nil))

(defthmd myif-push-true
  (equal (myif test x y)
         (myif test (push-true test x) y))
  :hints (("Goal" :in-theory (enable push-true))))

;but then how do we get rid of the push-true??
(defthm push-true-of-myif
  (equal (push-true test (myif test x y))
         (push-true test x))
  :hints (("Goal" :in-theory (enable push-true))))

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
;;                             CDR-OF-TAKE-BECOMES-SUBRANGE-BETTER
;;                             TAKE-OF-NTHCDR-BECOMES-SUBRANGE
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

(in-theory (disable ARRAY-REDUCTION-WHEN-ALL-SAME-IMPROVED ARRAY-REDUCTION-WHEN-ALL-SAME))

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
                                  (NTH-OF-BV-ARRAY-WRITE-BECOMES-BV-ARRAY-READ
                                   BVCHOP-LIST-OF-TAKE ;looped!
                                   )))))

;(local (in-theory (disable LIST::UPDATE-NTH-EQUAL-REWRITE)))

(defthm firstn-of-take
  (implies (and (<= LEN1 LEN2)
                (natp len1)
                (natp len2))
           (equal (FIRSTN LEN1 (TAKE LEN2 LST))
                  (take LEN1 LST)))
  :hints (("Goal" :in-theory (enable take firstn))))


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
                                                         <-of-if-arg1)
                                  (bvchop-list-of-take
                                   ;;TAKE-OF-NTHCDR-BECOMES-SUBRANGE
                                   )))))

;ffixme looped: BVCHOP-LIST-OF-TAKE TAKE-OF-BVCHOP-LIST

(defthm bvchop-list-of-bv-array-write
  (implies (and (<= size1 size2)
                (natp size1)
                (integerp size2))
           (equal (bvchop-list size1 (bv-array-write size2 len index val lst))
                  (bv-array-write size1 len index val lst)))
  :hints (("Goal" :in-theory (enable bv-array-write))))

(in-theory (disable NTH-BECOMES-BV-ARRAY-READ))

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
  :hints (("Goal" :in-theory (e/d (;list::nth-with-large-index
                                   bv-array-read BVCHOP-WHEN-I-IS-NOT-AN-INTEGER)
                                  (;JVM::INT-LEMMA0
                                   NTH-OF-BV-ARRAY-WRITE-BECOMES-BV-ARRAY-READ
                                   )))))

(in-theory (disable size-non-negative-when-unsigned-byte-p-free)) ;this caused problems..

(defthm bv-array-write-of-bvchop-list-tighten
  (implies (and (unsigned-byte-p width2 val) ;what if this isn't true?
                (< 0 len)
                (integerp len)
                (natp index)
                (< index len)
                (<= width2 width1) ;handle the other case?
                (natp width2)
                (integerp width1)
                (equal len (len lst)) ;gross!
                )
           (equal (bv-array-write width1 len index val (bvchop-list width2 lst))
                  (bv-array-write width2 len index val lst)))
  :hints (("Goal" :in-theory (e/d (bv-array-write BVCHOP-WHEN-I-IS-NOT-AN-INTEGER update-nth2)
                                  (;JVM::INT-LEMMA0
                                   )))))



(defthmd nth2-becomes-bvnth-for-natps-dag
  (implies (and (syntaxp (quotep vals))
                (all-natp vals)
                (natp indexsize)
                (natp index)
                (< index (len vals))
                )
           (equal (nth2 indexsize index vals)
                  (bvnth (width-of-widest-int vals)
                         indexsize
                         index
                         vals)))
  :hints (("Goal"
           :cases ((<= (bvchop indexsize index) index))
           :in-theory (enable nth2 bvnth all-integerp-when-all-natp))))




;see BVXOR-WITH-SMALL-ARG2 for a better way to do these:





;; (defthm getbit-when-arg1-is-not-a-natp
;;   (implies (not (natp size))
;;            (equal (getbit size val)
;;                   0))
;;   :hints
;;   (("Goal" :in-theory (e/d (getbit slice logtail)
;;                            (slice-becomes-getbit bvchop-1-becomes-getbit
;;                                                BVCHOP-OF-LOGTAIL-BECOMES-SLICE ;add to anti-slice
;;                                                anti-slice)))))



;bvchop analogue?
(defthm bv-array-read-of-getbit-when-len-is-2
  (equal (bv-array-read element-size 2 (getbit 0 x) lst)
         (bv-array-read element-size 2 x lst))
  :hints (("Goal" :in-theory (e/d (bv-array-read bvchop-when-i-is-not-an-integer getbit-when-val-is-not-an-integer)
                                  (NTH-OF-BV-ARRAY-WRITE-BECOMES-BV-ARRAY-READ)))))



;; (defthm take-of-logext-list
;;   (implies (and (<= n (len lst)) (natp n))
;;            (equal (take n (logext-list size lst))
;;                   (logext-list size (take n lst))))
;;   :hints (("Goal" :in-theory (e/d (take logext-list) (take-of-cdr-becomes-subrange)))))


;bozo add consp of bvchop-list?

(theory-invariant (incompatible (:definition UPDATE-NTH2) (:rewrite UPDATE-NTH-BECOMES-UPDATE-NTH2-EXTEND-GEN)))

;; (defthm cdr-of-update-nth2
;;   (implies (and (posp len)
;;                 (< n len))
;;            (equal (cdr (update-nth2 len n val list))
;;                   (if (zp len)
;;                       nil
;;                     (if (zp n)
;;                         (take (+ -1 len) (cdr list))
;;                         (update-nth2 len (+ -1 n) val (cdr list))))))
;;   :hints (("Goal" :in-theory (e/d (update-nth2 posp) (update-nth-becomes-update-nth2-extend-gen)))))


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

(defthm nth-when-all-equal$-helper
  (implies (and (all-equal$ val data)
                (syntaxp (not (equal val `(nth ,index ,data)))) ;helps prevent loops
                (natp index)
                (< index (len data))
                )
           (equal (nth index data)
                  val))
  :hints (("Goal" :in-theory (e/d (all-equal$ nth) (NTH-OF-CDR)))))

(in-theory (disable all-equal$))

(defthm nth-when-all-equal$
  (implies (and (all-equal$ val data)
                (syntaxp (not (equal val `(nth ,index ,data)))) ;helps prevent loops
;                (natp index)
                (< index (len data))
                )
           (equal (nth index data)
                  (if (equal 0 (len data))
                      nil
                  val)))
  :otf-flg t
  :hints (("Goal" :use (:instance  nth-when-all-equal$-helper (index (nfix index)))
           :in-theory (e/d (;NTH-WHEN-N-IS-ZP
                            )( nth-when-all-equal$-helper CAR-BECOMES-NTH-OF-0)))))

;; (thm
;;  (implies (and (equal (len x) (max (+ 1 (nfix key)) (len l)))
;;                (natp key))
;;           (equal (myif test x (jvm::update-nth-local key val l))
;;                  (jvm::update-nth-local key (myif test (nth key x) val) (myif test x l))))
;;  :otf-flg t
;;  :hints (("Goal" :in-theory (e/d (len-update-nth myif list::update-nth-equal-rewrite nth-when-n-is-zp) (car-becomes-nth-of-0)))))


(defthmd take-opener
  (implies (not (zp n))
           (equal (take n lst)
                  (cons (nth 0 lst)
                        (take (+ -1 n) (cdr lst)))))
  :hints (("Goal" :in-theory (enable take))))

;slowish proof
(defthmd nthcdr-opener
  (implies (not (zp n))
           (equal (nthcdr n l)
                  (nthcdr (+ n -1) (cdr l))))
  :hints (("Goal" :in-theory (e/d (nthcdr) (nthcdr-of-cdr-combine NTHCDR-OF-CDR-COMBINE-strong ;LIST::LEN-OF-NON-CONSP
                                                                  )))))

(theory-invariant (incompatible (:rewrite NTHCDR-OPENER) (:rewrite |3-CDRS|)))

;(local (in-theory (disable JVM::INT-LEMMA0)))

(defthmd bv-array-read-blast-one-step
  (implies (and (equal len (expt 2 index-width))
;               (equal index-width 4)
                (all-unsigned-byte-p index-width vals)
                (posp index-width)
                (equal (expt 2 index-width) (len vals))
                (natp index)
                )
           (equal (bv-array-read 1 len index vals)
                  (bif (getbit (+ -1 index-width) index)
                       (bv-array-read 1 (expt 2 (+ -1 index-width))
                                      (bvchop (+ -1 index-width) index)
                                      (subrange (expt 2 (+ -1 index-width))
                                                (+ -1 (expt 2 index-width))
                                                vals))
                       (bv-array-read 1 (expt 2 (+ -1 index-width))
                                      (bvchop (+ -1 index-width) index)
                                      (subrange 0 (+ -1 (expt 2 (+ -1 index-width)))
                                                vals)))))
  :hints (("Goal"
           :use ( ;; (:instance BVCAT-SPECIAL-OPENER
                 ;;                           (x (getbit (+ -1 index-width) index))
                 ;;                           (y (bvchop (+ -1 index-width) index))
                 ;;                           (n (+ -1 index-width)))
                 (:instance BVCAT-OF-GETBIT-AND-X-ADJACENT
                            (n (+ -1 index-width))
                            (x index)))
;          :expand ((BVCAT 1 0 7 INDEX))
           :in-theory (e/d (subrange
                            bif
                            bv-ARRAY-READ
                            ;LOGAPP-0
                            ceiling-of-lg
                            bvcat logapp
;bvcat
                            )
                           (;bif-rewrite
                            NTH-OF-BV-ARRAY-WRITE-BECOMES-BV-ARRAY-READ
                            BVCAT-OF-GETBIT-AND-X-ADJACENT
                            TIMES-4-BECOMES-LOGAPP
                            BVCAT-OF-GETBIT-AND-X-ADJACENT
                            BVCAT-EQUAL-REWRITE BVCAT-EQUAL-REWRITE-alt
                            LOGAPP-EQUAL-REWRITE
                            BVCAT-OF-0
                            )))))

;actually matches
(defthmd bv-array-read-blast-one-step-better
  (implies (and (equal len (expt 2 (+ -1 (integer-length len))))
             ;               (equal (+ -1 (integer-length len)) 4)
                (all-unsigned-byte-p (+ -1 (integer-length len)) vals)
                (posp (+ -1 (integer-length len)))
                (equal (expt 2 (+ -1 (integer-length len))) (len vals))
                (natp index)
                )
           (equal (bv-array-read 1 len index vals)
                  (bif (getbit (+ -1 (+ -1 (integer-length len))) index)
                       (bv-array-read 1
                                      (expt 2 (+ -1 (+ -1 (integer-length len))))
                                      (bvchop (+ -1 (+ -1 (integer-length len))) index)
                                      (subrange (expt 2 (+ -1 (+ -1 (integer-length len)))) (+ -1 (expt 2 (+ -1 (integer-length len)))) vals))
                       (bv-array-read 1
                                      (expt 2 (+ -1 (+ -1 (integer-length len))))
                                      (bvchop (+ -1 (+ -1 (integer-length len))) index)
                                      (subrange 0 (+ -1 (expt 2 (+ -1 (+ -1 (integer-length len))))) vals)))))
  :hints (("Goal" :use (:instance bv-array-read-blast-one-step (index-width (+ -1 (integer-length len)))))))
;bozo use the macros below more?

(defthm bv-array-clear-of-bv-array-write
  (implies (and (not (equal key1 key2))
                (natp esize)
                (natp key1)
                (< key1 len)
                (natp key2)
                (< key2 len)
                (natp len)
                (equal len (len lst)))
           (equal (bv-array-clear esize len key1 (bv-array-write esize len key2 val lst))
                  (bv-array-write esize len key2 val (bv-array-clear esize len key1 lst))))
  :hints (("Goal" :cases ((< KEY1 KEY2)
                          (< KEY2 KEY1)
                          )
           :in-theory (e/d (BV-ARRAY-CLEAR ;bv-array-write
                            BV-ARRAY-WRITE-OF-BV-ARRAY-WRITE-DIFF ;could this ever loop?  make a syntaxp version for non constants?
                            )
                           (BV-ARRAY-WRITE-OF-BV-ARRAY-WRITE-DIFF-CONSTANT-INDICES-GEN)))))

(defthm bv-array-clear-of-bv-array-write-same
  (implies (and (natp esize)
                (< key len)
                (natp key)
                (natp len)
                (equal len (len lst)))
           (equal (bv-array-clear esize len key (bv-array-write esize len key val lst))
                  (bv-array-clear esize len key lst)))
  :hints (("Goal" :cases ((< KEY1 KEY2)
                          (< KEY2 KEY1)
                          )
           :in-theory (e/d (BV-ARRAY-CLEAR) (BV-ARRAY-WRITE-OF-BV-ARRAY-WRITE-DIFF-CONSTANT-INDICES-GEN)))))

;; (thm
;;  (implies (and (EQUAL (CDR LST) (CDR RHS))
;;                (consp lst)
;;                (consp rhs))
;;           (EQUAL (LEN LST) (LEN RHS)))
;;  :hints (("Goal" :in-theory (e/d (len) (LEN-OF-CDR-BETTER LIST::LEN-OF-CDR)))))

(defthm true-listp-of-cdr-when-consp
  (implies (consp x)
           (equal (true-listp (cdr x))
                  (true-listp x))))

(defthm equal-of-true-listp-when-equal-of-cdr
  (IMPLIES (AND (EQUAL (CDR LST) (CDR RHS))
                (< 0 (LEN LST))
                (< 0 (LEN RHS)))
           (equal (equal (TRUE-LISTP RHS) (TRUE-LISTP LST))
                  t))
  :hints (("Goal" :induct t
           :in-theory (enable true-listp))))

;; (thm
;;  (implies (and (equal (update-nth key v lst)
;;                       (update-nth key v rhs))
;;                (natp key)
;;                (< key (len lst))
;;                (< key (len rhs))
;;                )
;;           (iff (true-listp rhs)
;;                (true-listp lst)))
;;  :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;           :induct t
;;           :in-theory (e/d (update-nth all-unsigned-byte-p TRUE-LISTP-OF-CDR)
;;                           (LIST::EQUAL-APPEND-REDUCTION!-ALT
;;                            LIST::EQUAL-APPEND-REDUCTION!
;;                            UPDATE-NTH-BECOMES-UPDATE-NTH2-EXTEND-GEN)))))


;; (thm
;;  (implies (and (equal (update-nth key v lst)
;;                       (update-nth key v rhs))
;;                (natp key)
;;                (< key (len lst))
;;                (< key (len rhs))
;;                )
;;           (iff (all-unsigned-byte-p esize rhs)
;;                (all-unsigned-byte-p esize lst)))
;;  :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;           :induct t
;;           :in-theory (e/d (update-nth all-unsigned-byte-p) ()))))



(in-theory (disable TRUE-LISTP))

(defthm equal-of-len-and-len-when-equal-of-nthcdr-and-nthcdr
  (implies (and (equal (nthcdr n x) (nthcdr n y))
                (or (< n (len x))
                    (< n (len y))))
           (equal (equal (len x) (len y))
                  t))
  :hints (("Goal" :in-theory (enable nthcdr))))



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
                                                  ;LIST::UPDATE-NTH-EQUAL-REWRITE ;loops with list::clear-nth?
                                           ;;list::clear-nth
                                                  UPDATE-NTH-WHEN-EQUAL-OF-NTH
                                                  )
                                  (NTH-OF-BV-ARRAY-WRITE-BECOMES-BV-ARRAY-READ
                                   UPDATE-NTH-BECOMES-UPDATE-NTH2-EXTEND-GEN
                                   ;LIST::CLEAR-NTH-EQUAL-CLEAR-NTH-REWRITE
                                   )))))

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
;;   :otf-flg t
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
;;                             BVCHOP-LIST-OF-TAKE ;bozo looped
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

(defthm all-unsigned-byte-p-of-bv-array-clear-gen
  (implies (and (<= element-size size)
                (natp size)
                (natp element-size))
           (equal (all-unsigned-byte-p size (bv-array-clear element-size len key lst))
                  t))
  :hints (("Goal" :in-theory (enable bv-array-clear))))


(defthm trim-of-bv-array-read
  (equal (trim n (bv-array-read element-size len index data))
         (bv-array-read (min (nfix n) (ifix element-size)) len index data))
  :hints (("Goal" :in-theory (e/d (trim natp bvchop-of-bv-array-read)
                                  (;list::nth-of-cons
                                   )))))

;; (thm
;;  (IMPLIES (and (EQUAL free (BVCHOP 5 X))
;;                (syntaxp (and (quotep free)
;;                              (not (quotep x)))))
;;           (EQUAL (BVSHL 32 X SHIFT-AMOUNT)
;;                  (BVSHL 32 free SHIFT-AMOUNT)))
;;  :hints (("Goal" :in-theory (enable bvshl))))

(defthm bv-array-read-when-arg3-not-integer
  (implies (not (integerp arg3))
           (equal (bv-array-read arg1 arg2 arg3 arg4)
                  (bv-array-read arg1 arg2 0 arg4)))
  :hints (("Goal" :in-theory (e/d (bv-array-read) (NTH-OF-BV-ARRAY-WRITE-BECOMES-BV-ARRAY-READ)))))

;what do we want to happen in this case?
;; (defthm bv-array-read-when-arg3-negative
;;   (implies (< arg3 0)
;;            (equal (bv-array-read arg1 arg2 arg3 arg4)
;;                   (bv-array-read arg1 arg2 0 arg4)))
;;   :hints (("Goal" :in-theory (enable bv-array-read))))

(defthmd nth-unroll
  (implies (not (zp n))
           (equal (nth n l)
                  (nth (- n 1) (cdr l)))))



;; (defthm bv-array-read-of-logext-list-gen
;;   (implies (and (<= size size2)
;;                 (equal len (len lst))
;;                 (natp size)
;;                 (integerp size2))
;;            (equal (bv-array-read size len index (logext-list size2 lst))
;;                   (bv-array-read size len index lst)))
;;   :otf-flg t
;;   :hints
;;   (("Goal" :cases ((equal 0 (len lst))) ;yuck
;;     :in-theory (e/d (bvchop-when-i-is-not-an-integer
;;                        bv-array-read) (NTH-OF-BV-ARRAY-WRITE-BECOMES-BV-ARRAY-READ)))))


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
;;                                  (BVCHOP-1-BECOMES-GETBIT SLICE-BECOMES-GETBIT
;;                                                          LOGTAIL-OF-BVCHOP-BECOMES-SLICE
;;                                                          BVCHOP-OF-LOGTAIL-BECOMES-SLICE
;;                                                          SLICE-BECOMES-BVCHOP
;;                                                          BVCHOP-OF-LOGTAIL-BECOMES-SLICE
;;                                                          anti-bvplus)))))

(defthm bv-array-read-of-logext-arg3
  (implies (and (integerp index)
                (integerp width2)
                (<= (integer-length (+ -1 len)) width2))
           (equal (bv-array-read width len (logext width2 index) data)
                  (bv-array-read width len index data)))
  :hints (("Goal" :in-theory (e/d (bv-array-read ceiling-of-lg) (NTH-OF-BV-ARRAY-WRITE-BECOMES-BV-ARRAY-READ)))))


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

(in-theory (disable BVCHOP-LIST-OF-TAKE))
(theory-invariant (incompatible (:rewrite BVCHOP-LIST-OF-TAKE) (:rewrite TAKE-OF-BVCHOP-LIST)))

(defthm all-unsigned-byte-p-when-not-integerp-width
  (implies (not (integerp width))
           (equal (all-unsigned-byte-p width data)
                  (endp data)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable all-unsigned-byte-p))))

(defthm all-unsigned-byte-p-when-negative-width
  (implies (< width 0)
           (equal (all-unsigned-byte-p width data)
                  (endp data)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable all-unsigned-byte-p))))

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
                            ;TAKE-OF-NTHCDR-BECOMES-SUBRANGE
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
                            ;TAKE-OF-NTHCDR-BECOMES-SUBRANGE
                            ;CDR-OF-TAKE-BECOMES-SUBRANGE-BETtER ;bozo ;also bozo on the non better
                            UPDATE-NTH-BECOMES-UPDATE-NTH2-EXTEND-GEN)))))

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
                                   ;TAKE-OF-NTHCDR-BECOMES-SUBRANGE
                                   ;CDR-OF-TAKE-BECOMES-SUBRANGE-BETtER ;bozo
                                   ;CDR-OF-TAKE-BECOMES-SUBRANGE ;bozo
                                   UPDATE-NTH-BECOMES-UPDATE-NTH2-EXTEND-GEN)))))

(in-theory (disable subrange)) ;move

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

;move
(defthm cdr-of-bv-array-write-better
  (implies (and (integerp len)
                (< key len)
                (natp key))
           (equal (cdr (bv-array-write element-size len key val lst))
                  (if (zp len)
                      nil
                    (if (< key 1)
                        (bvchop-list element-size (cdr (take len (true-list-fix lst))))
                      (bv-array-write element-size (- len 1) (- key 1) val (nthcdr 1 lst))))))
  :otf-flg t
  :hints (("Goal"
           :cases ((and (< len 0)
                        (< key n))
                   (and (not (< len 0))
                        (< key n))
                   (and (< len 0)
                        (not (< key n)))
                   (and (not (< len 0))
                        (not (< key n))))
           :in-theory (e/d (update-nth2 bv-array-write-opener
                            ;bv-array-write
                            ) (ceiling-of-lg
                               update-nth-becomes-update-nth2-extend-gen
                            ;LIST::UPDATE-NTH-EQUAL-REWRITE-ALT
                            ;LIST::UPDATE-NTH-EQUAL-REWRITE
                            )))))

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

(in-theory (disable USBP8-IMPLIES-SBP32-2))

(defthm equal-of-nth-and-bv-array-read
  (implies (and (<= len (len x))
                (all-unsigned-byte-p size x)
                (natp n)
                (natp len)
                (< n len) ;move
                )
           (equal (equal (nth n x) (bv-array-read size len n x))
                  t))
  :hints (("Goal" :in-theory (e/d (bv-array-read-opener)
                                  (NTH-OF-BV-ARRAY-WRITE-BECOMES-BV-ARRAY-READ)))))

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
  :hints (("Goal" :in-theory (e/d (bv-array-read-opener ;LIST::NTH-WITH-LARGE-INDEX
                                   ) (NTH-OF-BV-ARRAY-WRITE-BECOMES-BV-ARRAY-READ)))))

(defthm equal-of-bvchop-of-nth-and-bv-array-read
  (implies (and (equal len (len x)) ;relax?
                (natp len)
                (natp n))
           (equal (equal (bvchop size (nth n x)) (bv-array-read size len n x))
                  (if (< n len)
                      t
                    (equal 0 (bv-array-read size len n x)))))
  :hints (("Goal" :use (:instance equal-of-bvchop-of-nth-and-bv-array-read-helper)
           :in-theory (e/d (;LIST::NTH-WITH-LARGE-INDEX
                            )( equal-of-bvchop-of-nth-and-bv-array-read-helper)))))

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

(defstub error-state-no-params () t)

;; ;fixme - handle this stuff better?
;; (skip -proofs
;;  (defthm error-state-drop-params
;;    (equal (jvm::error-state msg state)
;;           (error-state-no-params))))


(defthm unsigned-byte-p-forced-of-bv-array-read
  (implies (and (<= element-size n)
                (natp n)
                (natp element-size))
           (equal (unsigned-byte-p-forced n (bv-array-read element-size len index data))
                  t))
  :hints (("Goal" :in-theory (e/d (unsigned-byte-p-forced) ()))))

(defthm force-of-non-nil
  (implies x
           (equal (force x)
                  x)))

;(in-theory (disable CDR-OF-TAKE-BECOMES-SUBRANGE)) ;drop?

;(local (in-theory (disable +-becomes-bvplus-hack))) ;drop?

;gen!
(defthm nth2-of-bv-array-write
  (implies (and (natp index)
                (< index 64)
                )
           (equal (nth2 '6 index (bv-array-write '16 '64 index2 val array))
                  (bv-array-read '16 '64 index (bv-array-write '16 '64 index2 val array))))
  :hints (("Goal" :in-theory (enable ;BV-ARRAY-READ
                              nth2))))

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
                     NTH-OF-BV-ARRAY-WRITE-BECOMES-BV-ARRAY-READ
                     UPDATE-NTH-BECOMES-UPDATE-NTH2-EXTEND-GEN
                     )))))

;move a bunch of this stuff

(defthm bv-array-write-of-0-and-bvchop-list
  (implies (and (<= element-size2 element-size1)
                (natp element-size2)
                (natp index2)
                (natp element-size1))
           (equal (bv-array-write element-size1 len index2 0 (bvchop-list element-size2 lst))
                  (bv-array-write element-size2 len index2 0 lst)))
  :hints (("Goal" :cases ((< len (len lst)))
           :in-theory (e/d (bv-array-write update-nth2 BVCHOP-LIST-OF-TAKE-OF-BVCHOP-LIST-GEN)
                           (update-nth-becomes-update-nth2-extend-gen)))))

(defthm bv-array-write-of-0-and-bv-array-write-tighter
  (implies (and (< element-size2 element-size1) ;true for = but would loop
                (natp element-size2)
                (natp index2)
                (natp element-size1))
           (equal (BV-ARRAY-WRITE ELEMENT-SIZE1 LEN INDEX2 0 (BV-ARRAY-WRITE ELEMENT-SIZE2 LEN INDEX1 0 LST))
                  (BV-ARRAY-WRITE ELEMENT-SIZE2 LEN INDEX2 0 (BV-ARRAY-WRITE ELEMENT-SIZE2 LEN INDEX1 0 LST))
                  ))
  :hints (("Goal" :cases ((< len (len lst)))
           :in-theory (e/d (bv-array-write update-nth2) (update-nth-becomes-update-nth2-extend-gen)))))

(defthm bv-array-write-of-bv-array-write-diff-same-val
  (implies (and (syntaxp (smaller-termp index2 index1))
                (< index1 len)
                (< index2 len)
                (natp index1)
                (natp index2)
                (natp len)
                (natp element-size))
           (equal (bv-array-write element-size len index1 val (bv-array-write element-size len index2 val lst))
                  (bv-array-write element-size len index2 val (bv-array-write element-size len index1 val lst))))
  :hints
  (("Goal"
    :in-theory (e/d (update-nth2 ;list::update-nth-update-nth-diff
                     bv-array-write)
                    (UPDATE-NTH-BECOMES-UPDATE-NTH2-EXTEND-GEN
                     BV-ARRAY-WRITE-EQUAL-REWRITE-ALT
                     BV-ARRAY-WRITE-EQUAL-REWRITE)))))

(defthm bv-array-clear-of-bv-array-clear-diff
  (implies (and (syntaxp (smaller-termp index2 index1))
                (<= element-size2 element-size1) ;other case?
                (< index1 len)
                (< index2 len)
                (natp index1)
                (natp index2)
                (natp len)
                (natp element-size1)
                (natp element-size2))
           (equal (bv-array-clear element-size1 len index1 (bv-array-clear element-size2 len index2 lst))
                  (bv-array-clear element-size2 len index2 (bv-array-clear element-size2 len index1 lst))))
  :hints (("Goal"
           :use (:instance bv-array-write-of-bv-array-write-diff-constant-indices-gen (val1 0) (val2 0))
           :cases ((equal element-size1 element-size2))
           :in-theory (e/d (bv-array-clear)
                           (bv-array-write-of-bv-array-write-diff-constant-indices-gen
                            BV-ARRAY-WRITE-EQUAL-REWRITE-ALT BV-ARRAY-WRITE-EQUAL-REWRITE)))))

(defthm bv-array-clear-of-bv-array-clear-diff-constant-indices
  (implies (and (syntaxp (quotep index1))
                (syntaxp (quotep index2))
                (< index2 index1)
                (<= element-size2 element-size1) ;other case?
                (< index1 len)
                (< index2 len)
                (natp index1)
                (natp index2)
                (natp len)
                (natp element-size1)
                (natp element-size2))
           (equal (bv-array-clear element-size1 len index1 (bv-array-clear element-size2 len index2 lst))
                  (bv-array-clear element-size2 len index2 (bv-array-clear element-size2 len index1 lst))))

  :hints (("Goal" :use (:instance bv-array-clear-of-bv-array-clear-diff)
           :in-theory (disable bv-array-clear-of-bv-array-clear-diff))))

(defthm bv-array-clear-of-bvchop-list
  (equal (bv-array-clear esize len key (bvchop-list esize lst))
         (bv-array-clear esize len key lst))
  :hints (("Goal"
           :cases ((not (natp esize)) (<= len (len lst)))
           :in-theory (e/d (bv-array-clear
                            bv-array-write ;fixme
                            update-nth2
                            BVCHOP-LIST-OF-TAKE-OF-BVCHOP-LIST-GEN
                            natp)
                           (update-nth-becomes-update-nth2-extend-gen
                            ;list::open-equiv ;yuck?
                            )))))

(defthm bv-array-clear-of-take
  (implies (natp key)
           (equal (bv-array-clear esize len key (take len lst))
                  (bv-array-clear esize len key lst)))
  :hints (("Goal" :in-theory (e/d (bv-array-clear
                                   bv-array-write ;fixme
                                   update-nth2) (update-nth-becomes-update-nth2-extend-gen)))))

(defthm bv-array-clear-range-same
  (implies (natp key)
           (equal (bv-array-clear-range esize len key key lst)
                  (bv-array-clear esize len key lst)))
  :hints (("Goal" :expand ( (bv-array-clear-range esize len key key lst)))))

(defthm bv-array-clear-of-bv-array-clear-adjacent1
  (implies (and (equal index2 (+ 1 index1))
                (< index1 len)
                (< index2 len)
                (natp elem-size)
                (natp len)
                (natp index1)
                (natp index2))
           (equal (bv-array-clear elem-size len index1 (bv-array-clear elem-size len index2 lst))
                  (bv-array-clear-range elem-size len index1 index2 lst))))

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
                  (bv-array-clear-range elem-size len index1 highindex lst))))

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
                  (bv-array-clear-range elem-size len lowindex index1 lst))))

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
                  (bv-array-clear elem-size len index1 (bv-array-clear-range elem-size len lowindex highindex lst)))))

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
  :hints (("Goal" :in-theory (disable bv-array-clear-of-bv-array-clear-range-adjacent1 bv-array-clear-of-bv-array-clear-range-adjacent2))))

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

(defthm nth-of-bv-array-clear
  (implies (and (< n len)
                (natp len)
                (natp n))
           (equal (nth n (bv-array-clear elem-size len n lst))
                  0))
  :hints (("Goal" :in-theory (e/d (bv-array-clear bv-array-write update-nth2 ceiling-of-lg) (update-nth-becomes-update-nth2-extend-gen)))))

;could drop hyps if we change what bv-array-clear-range does in the base case
(defthm take-of-bv-array-clear-irrel
  (implies (and (<= index index2)
                (natp len)
                (< index2 len)
;                (<= len (len lst))
                (natp index)
                (natp index2))
           (equal (take index (bv-array-clear elem-size len index2 lst))
                  (bvchop-list elem-size (take index lst))))
  :hints (("Goal" :in-theory (e/d (bv-array-clear bv-array-write update-nth2 ceiling-of-lg) (update-nth-becomes-update-nth2-extend-gen)))))

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
  :hints (("Goal" :in-theory (e/d (bv-array-clear bv-array-write update-nth2 ceiling-of-lg
                                                  ;;natp
                                                  take
                                                  UNSIGNED-BYTE-P-OF-INTEGER-LENGTH-GEN)
                                  (update-nth-becomes-update-nth2-extend-gen
                                   EQUAL-OF-UPDATE-NTH
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
                  (bv-array-clear-range elem-size len lowindex1 highindex2 lst))))

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
                    (bv-array-clear-range elem-size len lowindex2 highindex2 lst)))))

(in-theory (disable bv-array-clear-range))

(defthm true-listp-of-bv-array-clear-range
  (implies (true-listp lst)
           (equal (true-listp (bv-array-clear-range elem-size len lowindex highindex lst))
                  t)))

(defthm nthcdr-of-bv-array-clear
  (implies (and (<= n len)
                (< key len)
                (integerp len)
                (natp n)
                (natp key))
           (equal (nthcdr n (bv-array-clear element-size len key lst))
                  (if (< key n)
                      (bvchop-list element-size
                                    (nthcdr n (take len (true-list-fix lst))))
                    (bv-array-clear element-size (- len n)
                                    (- key n) (nthcdr n lst)))))
  :hints (("Goal" :in-theory (enable bv-array-clear))))

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
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (bv-array-clear-range nthcdr) (NTHCDR-OF-CDR-COMBINE NTHCDR-OF-CDR-COMBINE-strong)))))

;(in-theory (disable LIST::EQUAL-APPEND-REDUCTION!-ALT)) ;move up?

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
           :in-theory (e/d (bv-array-clear-range nthcdr) (NTHCDR-OF-CDR-COMBINE
                                                          NTHCDR-OF-CDR-COMBINE-strong
                                                          ;TAKE-OF-NTHCDR-BECOMES-SUBRANGE
                                                          ;NTHCDR-OF-TAKE-BECOMES-SUBRANGE
                                                          )))))


(defthm nth-of-bv-array-clear-better
  (implies (and (natp len)
                (natp n))
           (equal (nth n (bv-array-clear elem-size len n lst))
                  (if (< n len)
                      0
                    nil)))
  :hints
  (("Goal" :in-theory
    (e/d (bv-array-clear bv-array-write ceiling-of-lg update-nth2)
         (update-nth-becomes-update-nth2-extend-gen)))))

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

(defthm nth-of-bv-array-clear-diff
  (implies (and (natp len)
                (natp n)
                (natp index)
;                (natp elem-size)
                (< n len)
                (< index len) ;Mon Jul 19 20:50:11 2010
                (not (equal n index))
                )
           (equal (nth n (bv-array-clear elem-size len index lst))
                  (bvchop elem-size (nth n lst))))
  :hints
  (("Goal" :in-theory
    (e/d (bv-array-clear bv-array-write-opener update-nth2)
         (update-nth-becomes-update-nth2-extend-gen)))))

(defthm nth-of-bv-array-clear-both
  (implies (and (natp len)
                (natp n)
                (natp index)
                (< index len) ;Mon Jul 19 20:50:11 2010
                (< n len)
                )
           (equal (nth n (bv-array-clear elem-size len index lst))
                  (if (equal n index)
                      0
                  (bvchop elem-size (nth n lst)))))
  :hints
  (("Goal" :in-theory
    (e/d (bv-array-clear bv-array-write-opener update-nth2)
         (update-nth-becomes-update-nth2-extend-gen)))))

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
  :hints
  (("Goal" :in-theory
    (e/d (bv-array-clear-range bv-array-write update-nth2)
         (update-nth-becomes-update-nth2-extend-gen)))))

(defthm car-of-BV-ARRAY-CLEAR-of-0
  (implies (posp len)
           (equal (CAR (BV-ARRAY-CLEAR ELEM-SIZE LEN 0 lst))
                  0))
  :hints (("Goal" :in-theory (enable BV-ARRAY-CLEAR))))

(defthm cdr-of-bv-array-clear-of-0
  (implies (posp len)
           (equal (cdr (bv-array-clear elem-size len 0 lst))
                  (bvchop-list elem-size (take (+ -1 len) (cdr lst)))))
  :hints (("Goal" :in-theory (enable bv-array-clear))))

(defthm car-of-BV-ARRAY-CLEAR-RANGE-of-0
  (implies (and (posp len)
                (natp highindex))
           (equal (CAR (BV-ARRAY-CLEAR-RANGE ELEM-SIZE LEN 0 HIGHINDEX LST))
                  0))
  :hints (("Goal" :expand (BV-ARRAY-CLEAR-RANGE ELEM-SIZE LEN 0 HIGHINDEX LST))))

(defthm cdr-of-bv-array-clear-2
  (implies (and (<= n len)
                (< key len)
                (integerp len)
                (natp key))
           (equal (cdr (bv-array-clear element-size len key lst))
                  (if (< key 1)
                      (bvchop-list element-size
                                   (cdr (take len (true-list-fix lst))))
                    (bv-array-clear element-size (- len 1)
                                    (- key 1) (cdr lst)))))
  :hints (("Goal" :in-theory (enable bv-array-clear))))

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

(defthmd take-when-most-known
  (implies (and (equal (take (+ -1 n) x) free)
                (posp n))
           (equal (take n x)
                  (append free
                          (list (nth (+ -1 n) x)))))
  :hints (("Goal" :in-theory (enable equal-of-append
;                                     subrange ;todo
                                     ))))

(defun sub1-sub1-induct (n1 n2)
  (if (zp n1)
      (list n1 n2)
    (sub1-sub1-induct (+ -1 n1) (+ -1 n2))))

;move
;todo: name clash
(defthm take-of-repeat-2
  (implies (and (<= n1 n2)
                (natp n1)
                (natp n2))
           (equal (take n1 (repeat n2 x))
                  (repeat n1 x)))
  :hints (("Goal" :induct (sub1-sub1-induct n1 n2)
           :in-theory (e/d (take repeat) (CAR-OF-TAKE-STRONG ;todo: looped
                                          TAKE-OF-CONS
                                          )))))

(defthm take-of-bv-array-clear-range
  (implies (and ; (natp elem-size)
            (natp n)
            (natp len)
            (natp highindex)
            (< highindex len)
            (<= n (+ 1 highindex)))
           (equal (take n (bv-array-clear-range elem-size len 0 highindex lst))
                  (repeat n 0)))
  :hints ( ("Goal" :induct t
           :do-not '(generalize eliminate-destructors)
           :in-theory (enable take bv-array-clear-range take-when-most-known equal-of-append))))

(defthm bv-array-clear-bottom-range
  (implies (and (posp len)
                (< i len)
                (natp i))
           (equal (bv-array-clear-range elem-size len 0 i lst)
                  (append (repeat (+ 1 i) 0)
                          (bvchop-list elem-size (subrange (+ 1 i) (+ -1 len) lst)))))
  :hints (("Goal" :in-theory (e/d (subrange TAKE-OF-CDR CAR-BECOMES-NTH-OF-0 equal-of-append)
                                  (cdr-of-take
                                   ;cdr-of-take-becomes-subrange-better
                                   ;NTHCDR-OF-TAKE-BECOMES-SUBRANGE
                                   ;TAKE-OF-NTHCDR-BECOMES-SUBRANGE
                                   ;;TAKE-OF-CDR-BECOMES-SUBRANGE
                                   )))))

;move
(defthm bv-array-write-of-true-list-fix
  (equal (bv-array-write elem-size len index val (true-list-fix lst))
         (bv-array-write elem-size len index val lst))
  :hints (("Goal" :in-theory (e/d (bv-array-write
                                   update-nth2
                                   ) (update-nth-becomes-update-nth2-extend-gen)))))

(defthm bv-array-clear-of-true-list-fix
  (equal (bv-array-clear elem-size len index (true-list-fix lst))
         (bv-array-clear elem-size len index lst))
  :hints (("Goal" :in-theory (e/d (bv-array-clear) ()))))

(defthm BV-ARRAY-CLEAR-RANGE-of-true-list-fix
  (implies (and (<= lowindex highindex)
                (natp lowindex)
                (natp highindex))
           (equal (BV-ARRAY-CLEAR-RANGE ELEM-SIZE len lowindex highindex (TRUE-LIST-FIX LST))
                  (BV-ARRAY-CLEAR-RANGE ELEM-SIZE len lowindex highindex LST)))
  :hints (("Goal" :in-theory (e/d (BV-ARRAY-CLEAR-RANGE) ()))))

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

(defthm take-of-firstn-same
  (equal (take n (firstn n x))
         (take n x))
  :hints (("Goal" :in-theory (enable take firstn))))

(defthm take-when-not-consp-cheap
  (implies (not (consp x))
           (equal (take n x)
                  (repeat n nil)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable take))))

(defthm bv-array-write-of-firstn
  (equal (bv-array-write element-size len index val (firstn len data))
         (bv-array-write element-size len index val data))
  :hints (("Goal" :in-theory (e/d (bv-array-write update-nth2) (update-nth-becomes-update-nth2-extend-gen)))))

(defthm bv-array-clear-of-firstn
  (equal (bv-array-clear element-size len index (firstn len data))
         (bv-array-clear element-size len index data))
  :hints (("Goal" :in-theory (e/d (bv-array-clear) ()))))

(defthm bv-array-clear-of-bv-array-write-better
  (implies (and (not (equal key1 key2))
                (natp esize)
                (natp key1)
                (< key1 len)
                (natp key2)
                (< key2 len)
                (natp len)
                (<= len (len lst)) ;drop?
                )
           (equal (bv-array-clear esize len key1 (bv-array-write esize len key2 val lst))
                  (bv-array-write esize len key2 val (bv-array-clear esize len key1 lst))))
  :hints (("Goal" :use (:instance bv-array-clear-of-bv-array-write (lst (firstn len lst)))
           :in-theory (disable bv-array-clear-of-bv-array-write
                               bv-array-write-equal-rewrite-alt
                               bv-array-write-equal-rewrite))))

(defthm bv-array-clear-of-bv-array-clear-same
  (implies (and (natp index)
                (natp len)
                (natp element-size))
           (equal (bv-array-clear element-size len index (bv-array-clear element-size len index lst))
                  (bv-array-clear element-size len index lst)))
  :hints (("Goal" :in-theory (e/d (bv-array-write bv-array-clear update-nth2) (update-nth-becomes-update-nth2-extend-gen)))))

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

(DEFTHM ALL-UNSIGNED-BYTE-P-OF-BV-ARRAY-CLEAR-range
  (IMPLIES (AND (<= ELEMENT-SIZE SIZE)
                (NATP SIZE)
                (NATP ELEMENT-SIZE))
           (EQUAL (ALL-UNSIGNED-BYTE-P SIZE (BV-ARRAY-CLEAR-range ELEMENT-SIZE LEN lowindex highindex LST))
                  T))
  :HINTS (("Goal" :IN-THEORY (ENABLE BV-ARRAY-CLEAR-range))))


;move these
;a hack for rc2, since we are no longer trimming array reads
(defthm bvplus-of-bv-array-read-arg1
  (implies (and (< n element-size)
                (natp n)
                (integerp element-size))
           (equal (bvplus n (bv-array-read element-size len index data) y)
                  (bvplus n (bv-array-read n
                                           len index data) y)))
  :hints (("Goal" :in-theory (e/d (bv-array-read natp)
                                  (;list::nth-of-cons
                                   NTH-OF-BV-ARRAY-WRITE-BECOMES-BV-ARRAY-READ
                                   )))))

(defthm bvplus-of-bv-array-read-arg2
  (implies (and (< n element-size)
                (natp n)
                (integerp element-size))
           (equal (bvplus n x (bv-array-read element-size len index data))
                  (bvplus n x (bv-array-read n len index data))))
  :hints (("Goal" :in-theory (e/d (bv-array-read natp)
                                  (;list::nth-of-cons
                                   NTH-OF-BV-ARRAY-WRITE-BECOMES-BV-ARRAY-READ)))))

;hack for rc2..
(defthmd bvuminus-of-bv-array-read
  (implies (and (< n element-size)
                (natp n)
                (integerp element-size))
           (equal (bvuminus n (bv-array-read element-size len index data))
                  (bvuminus n (bv-array-read n len index data))))
  :hints (("Goal" :in-theory (e/d (bv-array-read natp)
                                  (;list::nth-of-cons
                                   NTH-OF-BV-ARRAY-WRITE-BECOMES-BV-ARRAY-READ)))))

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



;fixme -add hyps
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
  :hints (("Goal" :in-theory (e/d (getbit-list
                                   ;;LIST::NTH-WITH-LARGE-INDEX
                                   natp posp bv-array-read GETBIT-WHEN-VAL-IS-NOT-AN-INTEGER BVCHOP-WHEN-I-IS-NOT-AN-INTEGER)
                                  (;LIST::NTH-OF-CONS
                                   NTH-OF-BV-ARRAY-WRITE-BECOMES-BV-ARRAY-READ)))))

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
  :hints (("Goal" :in-theory (enable GETBIT-OF-BV-ARRAY-READ-HELPER bvchop-of-bv-array-read))))

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
           (equal (unsigned-byte-p width (nth n (update-subrange2 len start end vals lst)))
                  t))
  :hints (("Goal" :in-theory (enable ;LIST::NTH-APPEND
                              ))))

(defthm bv-array-read-of-bv-array-write-same-work-hard
  (implies (and (natp index)
                (work-hard (< index len))
                (integerp len))
           (equal (bv-array-read width len index (bv-array-write width len index val lst))
                  (bvchop width val)))
  :hints (("Goal" :in-theory (e/d (bv-array-read-opener bv-array-write-opener) ()))))

;move these?
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

;this version sets the length param of the bv-array-read to be the right
;fixme allow the lens in the lhs to differ?
;move
(defthm bv-array-read-of-take-better
  (implies (and (posp len)
                (natp index)
                (work-hard (< index len))
                (<= len (len array)))
           (equal (bv-array-read elem-size len index (take len array))
                  (bv-array-read elem-size (len array) index array)))
  :hints (("Goal" :in-theory (e/d (bv-array-read-opener) (NTH-OF-BV-ARRAY-WRITE-BECOMES-BV-ARRAY-READ)))))

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
  :OTF-FLG T
  :HINTS
  (("Goal"
    :IN-THEORY
    (E/D (BV-ARRAY-READ-OPENER BVCHOP-WHEN-I-IS-NOT-AN-INTEGER)
         (NTH-OF-BV-ARRAY-WRITE-BECOMES-BV-ARRAY-READ
          ;;BVPLUS-RECOLLAPSE
          )))))

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
