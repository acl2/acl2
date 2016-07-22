;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")

(include-book "x86-row-wow-thms" :ttags :all :dir :proof-utils)
(include-book "general-memory-utils" :ttags :all :dir :proof-utils)

(local (include-book "gl-lemmas"))
(local (include-book "centaur/bitops/ihs-extensions" :dir :system))

;; ======================================================================

;; Lemmas about physical-address-p, physical-address-listp, and
;; create-physical-address-list: these are very similar to lemmas
;; about canonical addresses in programmer-level-memory-utils.lisp.

(defthm create-physical-address-list-open-1
  (implies (and (physical-address-p (+ n x))
                (natp n))
           (equal (create-physical-address-list 1 (+ n x))
                  (list (+ n x))))
  :hints (("Goal" :expand (create-physical-address-list 1 (+ n x)))))

(defthm physical-address-listp-fwd-chain-true-listp
  (implies (physical-address-listp x)
           (true-listp x))
  :rule-classes (:forward-chaining))

(defthm member-p-physical-address-p
  (implies (and (physical-address-listp x)
                (member-p e x))
           (physical-address-p e))
  :rule-classes (:type-prescription :forward-chaining))

(defthm member-p-physical-address-p-physical-address-listp
  (implies (member-p e (create-physical-address-list n prog-addr))
           (physical-address-p e))
  :rule-classes (:type-prescription :forward-chaining))

(defthm subset-p-physical-address-listp
  (implies (and (physical-address-listp y)
                (subset-p x y))
           (physical-address-listp x))
  :hints (("Goal" :in-theory (e/d (subset-p) ())))
  :rule-classes :forward-chaining)

(defthm subset-p-physical-address-listp-create-physical-address-list
  (implies (subset-p x (create-physical-address-list n prog-addr))
           (physical-address-listp x))
  :hints (("Goal" :in-theory (e/d ()
                                  (subset-p-physical-address-listp))
           :use ((:instance subset-p-physical-address-listp
                            (y
                             (create-physical-address-list
                              n prog-addr))))))
  :rule-classes :forward-chaining)

(local
 (defthmd member-p-physical-address-listp-helper
   (implies (and (integerp n)
                 (< 0 n)
                 (physical-address-p prog-addr)
                 (physical-address-p (+ -1 n prog-addr)))
            (equal (member-p addr
                             (create-physical-address-list n prog-addr))
                   (and (integerp addr)
                        (<= prog-addr addr)
                        (< addr (+ n prog-addr)))))))

(defthm member-p-physical-address-listp

  ;; Relieving the hypotheses of this rule will require some
  ;; arithmetic reasoning.  To establish whether addr is a member of
  ;; the physical address list, we'd have to see whether it falls in
  ;; the range described by the first two hypotheses.

  (implies (and (<= prog-addr addr)
                (< addr (+ n prog-addr))
                (integerp n)
                (physical-address-p prog-addr)
                (physical-address-p (+ -1 n prog-addr))
                (integerp addr))
           (equal (member-p addr (create-physical-address-list n prog-addr))
                  t))
  :hints (("Goal" :in-theory (e/d (member-p-physical-address-listp-helper)
                                  ()))))

(defthm not-member-p-physical-address-listp

  ;; Relieving the hypotheses of this rule will require some
  ;; arithmetic reasoning.  To establish whether addr is a member of
  ;; the physical address list, we'd have to see whether it falls in
  ;; the range described by the first two hypotheses.

  (implies (and (or (< addr prog-addr)
                    (<= (+ n prog-addr) addr))
                (integerp n)
                (< 0 n)
                (physical-address-p prog-addr)
                (physical-address-p (+ -1 n prog-addr)))
           (equal (member-p addr
                            (create-physical-address-list n prog-addr))
                  nil))
  :hints (("Goal" :in-theory (e/d
                              (member-p-physical-address-listp-helper)
                              ()))))

(defthm subset-p-two-create-physical-address-lists
  (implies (and (physical-address-p y)
                (physical-address-p (+ j y))
                (<= y x)
                (<= (+ i x) (+ j y))
                (integerp j))
           (subset-p (create-physical-address-list i x)
                     (create-physical-address-list j y)))
  :hints (("Goal" :in-theory (e/d (subset-p) nil))))


(defthm disjoint-p-two-create-physical-address-lists-thm-0
  (implies (and (physical-address-p y)
                (physical-address-p (+ j y))
                (integerp j)
                (< 0 j)
                (<= (+ i x) y))
           (disjoint-p (create-physical-address-list i x)
                       (create-physical-address-list j y)))
  :hints (("Goal" :in-theory (e/d (disjoint-p member-p) ()))))

(defthm disjoint-p-two-create-physical-address-lists-thm-1
  (implies (and (physical-address-p x)
                (physical-address-p y)
                (physical-address-p (+ i x))
                (integerp j)
                (< 0 j)
                (<= (+ j y) x))
           (disjoint-p (create-physical-address-list i x)
                       (create-physical-address-list j y)))
  :hints (("Goal" :in-theory (e/d (disjoint-p member-p) ()))))

(defthm physical-address-p-limits-thm-0
  (implies (and (physical-address-p x)
                (natp m)
                (< m n)
                (physical-address-p (+ n x)))
           (physical-address-p (+ m x))))

(defthm physical-address-p-limits-thm-1
  ;; i is positive, k is positive, k < i
  (implies (and (physical-address-p (+ i addr))
                (physical-address-p addr)
                (integerp k)
                (<= 0 k)
                (< k i))
           (physical-address-p (+ k addr))))

(defthm physical-address-p-limits-thm-2
  ;; i is negative, k is negative, k > i
  (implies (and (physical-address-p (+ i addr))
                (physical-address-p addr)
                (integerp k)
                (< i 0)
                (< k 0)
                (< i k))
           (physical-address-p (+ k addr))))

(defthm physical-address-p-limits-thm-3
  ;; i is negative, j is positive, i < k < j
  (implies (and (physical-address-p (+ i addr))
                (physical-address-p (+ j addr))
                (integerp addr)
                (integerp k)
                (< i k)
                (< k j))
           (physical-address-p (+ k addr))))

;; ======================================================================

;; RoW and WoW theorems:

;; First, some arithmetic lemmas for proving RoW/WoW theorems:

(defthm n32p-lower-16-val-logior-loghead-ash
  (implies (n32p val)
           (equal (logior (loghead 8 val)
                          (ash (loghead 8 (logtail 8 val)) 8))
                  (loghead 16 val))))

(defthm n32p-upper-16-val-logior-loghead-ash
  (implies (n32p val)
           (equal (logior (loghead 8 (logtail 16 val))
                          (ash (logtail 24 val) 8))
                  (logtail 16 val))))

(local
 (defthm n32p-upper-16-in-8s-val-logior-loghead-ash-helper
   (implies (n32p val)
            (equal (logior (loghead 8 val)
                           (ash (logtail 16 val) 16)
                           (ash (loghead 8 (logtail 8 val)) 8))
                   (logior (loghead 16 val)
                           (ash (logtail 16 val) 16))))
   :hints (("Goal"
            :in-theory (e/d ()
                            (n32p-lower-16-val-logior-loghead-ash
                             combining-logior-of-loghead-and-ash-loghead-logtail
                             combining-logior-of-loghead-and-ash-logtail
                             putting-logior-loghead-ash-logtail-together))
            :use ((:instance n32p-lower-16-val-logior-loghead-ash))))))


(defthm n32p-upper-16-in-8s-val-logior-loghead-ash
  (implies (n32p val)
           (equal (logior (loghead 8 val)
                          (ash (logtail 16 val) 16)
                          (ash (loghead 8 (logtail 8 val)) 8))
                  val)))

(local (in-theory (enable rm-low-32 rm-low-64 wm-low-32 wm-low-64)))

(defthm |(rm-low-32 addr2 (wm-low-32 addr1 val x86)) --- same addr|
  (implies (and (equal addr1 addr2)
                (force (n32p val))
                (force (physical-address-p addr2))
                (force (physical-address-p (+ 3 addr2)))
                (not (programmer-level-mode x86)))
           (equal (rm-low-32 addr2 (wm-low-32 addr1 val x86))
                  val))
  :hints (("Goal" :in-theory (e/d () (force (force))))))

(defthm |(rm-low-32 addr2 (wm-low-32 addr1 val x86)) --- disjoint addr|
  (implies (disjoint-p (addr-range 4 addr1)
                       (addr-range 4 addr2))
           (equal (rm-low-32 addr2 (wm-low-32 addr1 val x86))
                  (rm-low-32 addr2 x86)))
  :hints (("Goal" :in-theory (e/d () (force (force))))))

;; wm-low-32 WoW:

(defthm |(wm-low-32 addr2 val2 (wm-low-32 addr1 val1 x86)) --- same addr|
  (implies (equal addr1 addr2)
           (equal (wm-low-32 addr2 val2 (wm-low-32 addr1 val1 x86))
                  (wm-low-32 addr2 val2 x86)))
  :hints (("Goal" :in-theory (e/d () (force (force))))))

(defthm |(wm-low-32 addr2 val2 (wm-low-32 addr1 val1 x86)) --- disjoint addr|
  (implies (disjoint-p (addr-range 4 addr1)
                       (addr-range 4 addr2))
           (equal (wm-low-32 addr2 val2 (wm-low-32 addr1 val1 x86))
                  (wm-low-32 addr1 val1 (wm-low-32 addr2 val2 x86))))
  :rule-classes ((:rewrite :loop-stopper ((addr2 addr1)))))

;; Theorems about rm64 and wm64:

;; rm-low-64 and wm-low-64:

(defthm |(rm-low-64 addr2 (wm-low-64 addr1 val x86)) --- same addr|
  (implies (and (equal addr1 addr2)
                (force (n64p val))
                (force (physical-address-p addr2))
                (force (physical-address-p (+ 7 addr2)))
                (not (programmer-level-mode x86)))
           (equal (rm-low-64 addr2 (wm-low-64 addr1 val x86))
                  val))
  :hints (("Goal" :in-theory (e/d () (rm-low-32 wm-low-32)))))

(defthm |(rm-low-64 addr2 (wm-low-64 addr1 val x86)) --- disjoint addr|
  ;; Shilpi: Can the integerp hyps be removed somehow?
  (implies (and (disjoint-p (addr-range 8 addr1)
                            (addr-range 8 addr2))
                (integerp addr1)
                (integerp addr2))
           (equal (rm-low-64 addr2 (wm-low-64 addr1 val x86))
                  (rm-low-64 addr2 x86)))
  :hints (("Goal" :in-theory (e/d () (rm-low-32 wm-low-32)))))

;; wm-low-64 WoW:

(defthm |(wm-low-64 addr2 val2 (wm-low-64 addr1 val1 x86)) --- same addr|
  ;; Shilpi: Can the integerp hyp be removed somehow?
  (implies (and (equal addr1 addr2)
                (integerp addr1))
           (equal (wm-low-64 addr2 val2 (wm-low-64 addr1 val1 x86))
                  (wm-low-64 addr2 val2 x86)))
  :hints (("Goal" :in-theory (e/d () (rm-low-32 wm-low-32)))))

(defthm |(wm-low-64 addr2 val2 (wm-low-64 addr1 val1 x86)) --- disjoint addr|
  ;; Shilpi: Can the integerp hyps be removed somehow?
  (implies (and (disjoint-p (addr-range 8 addr1)
                            (addr-range 8 addr2))
                (integerp addr1)
                (integerp addr2))
           (equal (wm-low-64 addr2 val2 (wm-low-64 addr1 val1 x86))
                  (wm-low-64 addr1 val1 (wm-low-64 addr2 val2 x86))))
  :hints (("Goal" :in-theory (e/d () (rm-low-32 wm-low-32))))
  :rule-classes ((:rewrite :loop-stopper ((addr2 addr1)))))

;; Some theorems about the interaction of memi/!memi with
;; rm-low-32/rm-low-64/wm-low-32/wm-low-64 when the addresses are
;; disjoint:

(defthm |(rm-low-32 addr2 (xw :mem addr1 val x86)) --- disjoint addr|
  (implies (disjoint-p (addr-range 1 addr1)
                       (addr-range 4 addr2))
           (equal (rm-low-32 addr2 (xw :mem addr1 val x86))
                  (rm-low-32 addr2 x86)))
  :hints (("Goal" :in-theory (e/d () (force (force))))))

(defthm |(rm-low-64 addr2 (xw :mem addr1 val x86)) --- disjoint addr|
  (implies (disjoint-p (addr-range 1 addr1)
                       (addr-range 8 addr2))
           (equal (rm-low-64 addr2 (xw :mem addr1 val x86))
                  (rm-low-64 addr2 x86)))
  :hints (("Goal" :in-theory (e/d () (force (force))))))

(defthm |(xr :mem addr1 (wm-low-32 addr2 val x86)) --- disjoint addr|
  (implies (disjoint-p (addr-range 4 addr2)
                       (addr-range 1 addr1))
           (equal (xr :mem addr1 (wm-low-32 addr2 val x86))
                  (xr :mem addr1 x86)))
  :hints (("Goal" :in-theory (e/d (ifix) (force (force))))))

(defthm |(xr :mem addr1 (wm-low-64 addr2 val x86)) --- disjoint addr|
  (implies (disjoint-p (addr-range 8 addr2)
                       (addr-range 1 addr1))
           (equal (xr :mem addr1 (wm-low-64 addr2 val x86))
                  (xr :mem addr1 x86)))
  :hints (("Goal" :in-theory (e/d (ifix) (force (force))))))

(defthm |(xw :mem addr1 (wm-low-64 addr2 val x86)) --- disjoint addr|
  (implies (and (disjoint-p (addr-range 8 addr2)
                            (addr-range 1 addr1))
                (integerp addr1)
                (integerp addr2))
           (equal (wm-low-64 addr2 val2 (xw :mem addr1 val1 x86))
                  (xw :mem addr1 val1 (wm-low-64 addr2 val2 x86))))
  :hints (("Goal" :in-theory (e/d (ifix wm-low-64 wm-low-32) (force (force))))))

(local (in-theory (disable rm-low-32 rm-low-64 wm-low-32 wm-low-64)))

;; ======================================================================

;; Misc. lemmas:

;; TODO: These need to be placed in some coherent sense.

(defthm xr-mem-write-to-physical-memory-disjoint
  (implies (not (member-p index p-addrs))
           (equal (xr :mem index (write-to-physical-memory p-addrs bytes x86))
                  (xr :mem index x86)))
  :hints (("Goal" :in-theory (e/d* (member-p) (force (force))))))

(local
 (defthmd write-to-physical-memory-xw-mem-member-p-helper
   (implies (equal (write-to-physical-memory (cdr p-addrs)
                                             (cdr bytes)
                                             (xw :mem index byte
                                                 (xw :mem (car p-addrs)
                                                     (car bytes)
                                                     x86)))
                   (write-to-physical-memory (cdr p-addrs)
                                             (cdr bytes)
                                             (xw :mem (car p-addrs)
                                                 (car bytes)
                                                 x86)))
            (equal (write-to-physical-memory (cdr p-addrs)
                                             (cdr bytes)
                                             (xw :mem (car p-addrs)
                                                 (car bytes)
                                                 (xw :mem index byte x86)))
                   (write-to-physical-memory (cdr p-addrs)
                                             (cdr bytes)
                                             (xw :mem (car p-addrs)
                                                 (car bytes)
                                                 x86))))
   :hints (("Goal" :cases ((equal index (car p-addrs)))))))

(defthm write-to-physical-memory-xw-mem-member-p
  (implies (member-p index p-addrs)
           (equal (write-to-physical-memory p-addrs bytes (xw :mem index byte x86))
                  (write-to-physical-memory p-addrs bytes x86)))
  :hints (("Goal" :in-theory (e/d* (member-p write-to-physical-memory-xw-mem-member-p-helper) ()))))

(defthm rm-low-64-and-write-to-physical-memory-disjoint
  (implies (disjoint-p (addr-range 8 p-addr-1) p-addrs-2)
           (equal (rm-low-64 p-addr-1 (write-to-physical-memory p-addrs-2 bytes x86))
                  (rm-low-64 p-addr-1 x86)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (rm-low-64
                             rm-low-32
                             disjoint-p
                             rm-low-64-and-write-to-physical-memory-equal-helper-2)
                            (force (force))))))

(defthm rm-low-64-and-write-to-physical-memory-disjoint
  (implies (disjoint-p (addr-range 8 p-addr-1) p-addrs-2)
           (equal (rm-low-64 p-addr-1 (write-to-physical-memory p-addrs-2 bytes x86))
                  (rm-low-64 p-addr-1 x86)))
  :hints (("Goal" :in-theory (e/d* (rm-low-64 rm-low-32 disjoint-p)
                                   (force (force))))))

(defthm xr-mem-write-to-physical-memory-member
  (implies (and (member-p index p-addrs)
                (no-duplicates-p p-addrs))
           (equal (xr :mem index (write-to-physical-memory p-addrs bytes x86))
                  (nth (pos index p-addrs) bytes)))
  :hints (("Goal" :in-theory (e/d* (member-p pos) (force (force))))))

;; (local
;;  (defthm nth-0-xs
;;    (equal (nth 0 xs) (car xs))))

(local
 (defthmd rm-low-64-and-write-to-physical-memory-equal-helper-1
   (implies (and (byte-listp bytes)
                 (equal (len bytes) 8))
            (equal (combine-bytes (cdddr (cddddr bytes)))
                   (car (cdddr (cddddr bytes)))))))

(defthm rm-low-64-and-write-to-physical-memory-equal
  (implies (and (equal p-addrs-2 (addr-range 8 p-addr-1))
                (equal (len bytes) (len p-addrs-2))
                (byte-listp bytes)
                (not (programmer-level-mode x86)))
           (equal (rm-low-64 p-addr-1 (write-to-physical-memory p-addrs-2 bytes x86))
                  (combine-bytes bytes)))
  :hints (("Goal"
           :do-not '(preprocess)
           :do-not-induct t
           :use ((:instance rm-low-64-and-write-to-physical-memory-equal-helper-1))
           :in-theory (e/d* (rm-low-64
                             rm-low-32 member-p
                             rm-low-64-and-write-to-physical-memory-equal-helper-2)
                            (write-to-physical-memory
                             nth
                             force
                             (force)                             
                             member-p-cons
                             acl2::commutativity-of-logior
                             mv-nth-2-rcl-spec-16
                             write-to-physical-memory-xw-mem-member-p
                             (:linear bitops::logior-<-0-linear-2)
                             (:type-prescription bitops::logior-natp-type)
                             (:linear ash-monotone-2)
                             x86isa::combining-logior-of-loghead-and-ash-logtail
                             (:rewrite acl2::zip-open))))))

(defthm rm-low-32-and-xw-mem-disjoint
  (implies (disjoint-p (list index-2) (addr-range 4 index-1))
           (equal (rm-low-32 index-1 (xw :mem index-2 val-2 x86))
                  (rm-low-32 index-1 x86)))
  :hints (("Goal" :in-theory (e/d* (rm-low-32) ()))))

(defthm rm-low-64-and-xw-mem-disjoint
  ;; Reuse rm-low-32-and-xw-mem-disjoint here!
  (implies (disjoint-p (list index-2) (addr-range 8 index-1))
           (equal (rm-low-64 index-1 (xw :mem index-2 val-2 x86))
                  (rm-low-64 index-1 x86)))
  :hints (("Goal" :in-theory (e/d* (rm-low-64 rm-low-32) ()))))

(defthm xw-mem-and-wm-low-32-commute
  (implies (disjoint-p (list index-1) (addr-range 4 index-2))
           (equal (xw :mem index-1 val-1 (wm-low-32 index-2 val-2 x86))
                  (wm-low-32 index-2 val-2 (xw :mem index-1 val-1 x86))))
  :hints (("Goal" :in-theory (e/d* (wm-low-32) ()))))

(defthm xw-mem-and-wm-low-64-commute
  ;; Reuse xw-mem-and-wm-low-32-commute here!
  (implies (disjoint-p (list index-1) (addr-range 8 index-2))
           (equal (xw :mem index-1 val-1 (wm-low-64 index-2 val-2 x86))
                  (wm-low-64 index-2 val-2 (xw :mem index-1 val-1 x86))))
  :hints (("Goal" :in-theory (e/d* (wm-low-64 wm-low-32) ()))))

(defthm read-from-physical-memory-and-write-to-physical-memory-disjoint
  (implies (disjoint-p p-addrs-1 p-addrs-2)
           (equal (read-from-physical-memory
                   p-addrs-1
                   (write-to-physical-memory p-addrs-2 bytes x86))
                  (read-from-physical-memory p-addrs-1 x86)))
  :hints (("Goal" :in-theory (e/d* (disjoint-p) ()))))

(defthm assoc-list-and-create-phy-addr-bytes-alist
  (implies (and (true-listp y)
                (equal (len x) (len y))
                (no-duplicates-p x))
           (equal (assoc-list x (create-phy-addr-bytes-alist x y))
                  y)))

(defthm assoc-list-of-rev-of-create-phy-addr-bytes-alist
  (implies (and (true-listp y)
                (equal (len x) (len y))
                (no-duplicates-p x))
           (equal (assoc-list x (acl2::rev (create-phy-addr-bytes-alist x y)))
                  y)))

(defthm read-from-physical-memory-and-write-to-physical-memory-equal
  (implies (and (no-duplicates-p p-addrs)
                (physical-address-listp p-addrs)
                (equal (len p-addrs) (len bytes)))
           (equal (read-from-physical-memory p-addrs (write-to-physical-memory p-addrs bytes x86))
                  (assoc-list p-addrs (reverse (create-phy-addr-bytes-alist p-addrs bytes)))))
  :hints (("Goal"
           :induct (read-from-physical-memory p-addrs (write-to-physical-memory p-addrs bytes x86))
           :in-theory (e/d* (member-p) ()))))

;; ======================================================================

;; Relationship between wm-low-64 and write-to-physical-memory, and
;; rm-low-64 and read-from-physical-memory:

(defthmd rewrite-wm-low-64-to-write-to-physical-memory
  (implies (not (programmer-level-mode x86))
	   (equal (wm-low-64 index value x86)
		  (write-to-physical-memory (addr-range 8 index) (byte-ify 8 value) x86)))
  :hints (("Goal"
	   :in-theory (e/d* (write-to-physical-memory
			     wm-low-64
			     wm-low-32
			     byte-ify)
			    ()))))
(encapsulate
  ()

  ;; Rewriting read-from-physical-memory to rm-low-64:

  (local
   (defthm loghead-n-ash-x-m-where-m>=n
     (implies (and (natp n)
                   (natp m)
                   (<= n m))
              (equal (loghead n (ash x m))
                     0))
     :hints (("Goal" :in-theory
              (e/d* (ihsext-inductions ihsext-recursive-redefs)
                    ())))))

  (local
   (defthm logtail-n-memi-where-n>=8
     (implies (and (x86p x86)
                   (natp n)
                   (<= 8 n))
              (equal (logtail n (xr :mem index x86)) 0))
     :hints (("Goal" :in-theory
              (e/d* (ihsext-inductions ihsext-recursive-redefs)
                    ())))))

  (local
   (defthm rewrite-read-from-physical-memory-to-rm-low-64-helper-1
     (implies (and (not (programmer-level-mode x86))
                   (physical-address-p index)
                   (x86p x86))
              (equal (loghead 8 (rm-low-64 index x86))
                     (xr :mem index x86)))
     :hints (("Goal" :in-theory (e/d* (rm-low-64
                                       rm-low-32)
                                      ())))))

  (local
   (defthm rewrite-read-from-physical-memory-to-rm-low-64-helper-2
     (implies (and (not (programmer-level-mode x86))
                   (physical-address-p index)
                   (x86p x86))
              (equal (loghead 8 (logtail 8 (rm-low-64 index x86)))
                     (xr :mem (1+ index) x86)))
     :hints (("Goal" :in-theory (e/d* (rm-low-64
                                       rm-low-32)
                                      ())))))
  (local
   (defthm rewrite-read-from-physical-memory-to-rm-low-64-helper-3
     (implies (and (not (programmer-level-mode x86))
                   (physical-address-p index)
                   (x86p x86))
              (equal (loghead 8 (logtail 16 (rm-low-64 index x86)))
                     (xr :mem (+ 2 index) x86)))
     :hints (("Goal" :in-theory (e/d* (rm-low-64
                                       rm-low-32)
                                      ())))))
  (local
   (defthm rewrite-read-from-physical-memory-to-rm-low-64-helper-4
     (implies (and (not (programmer-level-mode x86))
                   (physical-address-p index)
                   (x86p x86))
              (equal (loghead 8 (logtail 24 (rm-low-64 index x86)))
                     (xr :mem (+ 3 index) x86)))
     :hints (("Goal" :in-theory (e/d* (rm-low-64
                                       rm-low-32)
                                      ())))))
  (local
   (defthm rewrite-read-from-physical-memory-to-rm-low-64-helper-5
     (implies (and (not (programmer-level-mode x86))
                   (physical-address-p index)
                   (x86p x86))
              (equal (loghead 8 (logtail 32 (rm-low-64 index x86)))
                     (xr :mem (+ 4 index) x86)))
     :hints (("Goal" :in-theory (e/d* (rm-low-64
                                       rm-low-32)
                                      ())))))
  (local
   (defthm rewrite-read-from-physical-memory-to-rm-low-64-helper-6
     (implies (and (not (programmer-level-mode x86))
                   (physical-address-p index)
                   (x86p x86))
              (equal (loghead 8 (logtail 40 (rm-low-64 index x86)))
                     (xr :mem (+ 5 index) x86)))
     :hints (("Goal" :in-theory (e/d* (rm-low-64
                                       rm-low-32)
                                      ())))))
  (local
   (defthm rewrite-read-from-physical-memory-to-rm-low-64-helper-7
     (implies (and (not (programmer-level-mode x86))
                   (physical-address-p index)
                   (x86p x86))
              (equal (loghead 8 (logtail 48 (rm-low-64 index x86)))
                     (xr :mem (+ 6 index) x86)))
     :hints (("Goal" :in-theory (e/d* (rm-low-64
                                       rm-low-32)
                                      ())))))
  (local
   (defthm rewrite-read-from-physical-memory-to-rm-low-64-helper-8
     (implies (and (not (programmer-level-mode x86))
                   (physical-address-p index)
                   (x86p x86))
              (equal (logtail 56 (rm-low-64 index x86))
                     (xr :mem (+ 7 index) x86)))
     :hints (("Goal" :in-theory (e/d* (rm-low-64
                                       rm-low-32)
                                      ())))))

  (local
   (defthmd rewrite-read-from-physical-memory-to-rm-low-64-helper
     (implies (and (physical-address-p index)
                   (equal p-addrs
                          (list index (+ 1 index)
                                (+ 2 index)
                                (+ 3 index)
                                (+ 4 index)
                                (+ 5 index)
                                (+ 6 index)
                                (+ 7 index)))
                   (not (programmer-level-mode x86))
                   (x86p x86))
              (equal (read-from-physical-memory p-addrs x86)
                     (byte-ify 8 (rm-low-64 index x86))))
     :hints (("Goal"
              :do-not-induct t
              :in-theory (e/d* (read-from-physical-memory
                                byte-ify)
                               ())))))

  (defthmd rewrite-read-from-physical-memory-to-rm-low-64
    (implies (and (equal p-addrs (addr-range 8 index))
                  (physical-address-p index)
                  (not (programmer-level-mode x86))
                  (x86p x86))
             (equal (read-from-physical-memory p-addrs x86)
                    (byte-ify 8 (rm-low-64 (car p-addrs) x86))))
    :hints (("Goal"
             :do-not-induct t
             :use ((:instance rewrite-read-from-physical-memory-to-rm-low-64-helper
                              (index (car p-addrs))))
             :in-theory (e/d* (create-physical-address-list
                               physical-address-listp
                               unsigned-byte-p)
                              ())))))

;; ======================================================================
