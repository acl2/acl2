;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")

(include-book "x86-row-wow-thms"
	      :ttags (:include-raw :undef-flg :syscall-exec :other-non-det))
(include-book "general-memory-utils" :ttags :all :dir :proof-utils)

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))

;; ===================================================================

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

(local (in-theory (e/d (n32p-upper-16-in-8s-val-logior-loghead-ash-helper
			n32p-upper-16-in-8s-val-logior-loghead-ash
			n32p-lower-16-val-logior-loghead-ash-helper
			n32p-lower-16-val-logior-loghead-ash
			n32p-upper-16-val-logior-loghead-ash-helper
			n32p-upper-16-val-logior-loghead-ash)
		       ())))

(local (in-theory (enable rm-low-32 rm-low-64 wm-low-32 wm-low-64)))

(defthm |(rm-low-32 addr2 (wm-low-32 addr1 val x86)) --- same addr|
  (implies (and (equal addr1 addr2)
		(force (n32p val))
		(force (physical-address-p addr2))
		(force (physical-address-p (+ 3 addr2))))
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
		(force (physical-address-p (+ 7 addr2))))
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
