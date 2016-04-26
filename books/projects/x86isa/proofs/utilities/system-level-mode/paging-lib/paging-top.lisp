;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")
(include-book "common-paging-lemmas" :ttags :all)
(include-book "la-to-pa-lemmas" :ttags :all)

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))

;; ======================================================================

;; Some lemmas about translation-governing-addresses:

(defthm translation-governing-addresses-for-page-table-and-xlate-equiv-memory
  (implies (xlate-equiv-memory x86-1 x86-2)
	   (equal (translation-governing-addresses-for-page-table lin-addr base-addr x86-1)
		  (translation-governing-addresses-for-page-table lin-addr base-addr x86-2)))
  :hints (("Goal" :in-theory (e/d* (translation-governing-addresses-for-page-table) ())))
  :rule-classes :congruence)

(defthm translation-governing-addresses-for-page-directory-and-xlate-equiv-memory
  (implies (xlate-equiv-memory x86-1 x86-2)
	   (equal (translation-governing-addresses-for-page-directory lin-addr base-addr x86-1)
		  (translation-governing-addresses-for-page-directory lin-addr base-addr x86-2)))
  :hints (("Goal" :in-theory (e/d* (translation-governing-addresses-for-page-directory)
				   (xlate-equiv-memory-and-xlate-equiv-entries-rm-low-64-with-page-directory-entry-addr))
	   :use ((:instance xlate-equiv-memory-and-xlate-equiv-entries-rm-low-64-with-page-directory-entry-addr)
		 (:instance xlate-equiv-entries-and-page-size
			    (e-1 (rm-low-64 (page-directory-entry-addr lin-addr base-addr) x86-1))
			    (e-2 (rm-low-64 (page-directory-entry-addr lin-addr base-addr) x86-2))))))
  :rule-classes :congruence)

(defthm translation-governing-addresses-for-page-dir-ptr-table-and-xlate-equiv-memory
  (implies (xlate-equiv-memory x86-1 x86-2)
	   (equal (translation-governing-addresses-for-page-dir-ptr-table lin-addr base-addr x86-1)
		  (translation-governing-addresses-for-page-dir-ptr-table lin-addr base-addr x86-2)))
  :hints (("Goal" :in-theory (e/d* (translation-governing-addresses-for-page-dir-ptr-table)
				   (xlate-equiv-memory-and-xlate-equiv-entries-rm-low-64-with-page-dir-ptr-table-entry-addr))
	   :use ((:instance xlate-equiv-memory-and-xlate-equiv-entries-rm-low-64-with-page-dir-ptr-table-entry-addr)
		 (:instance xlate-equiv-entries-and-page-size
			    (e-1 (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr) x86-1))
			    (e-2 (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr) x86-2))))))
  :rule-classes :congruence)

(defthm translation-governing-addresses-for-pml4-table-and-xlate-equiv-memory
  (implies (xlate-equiv-memory x86-1 x86-2)
	   (equal (translation-governing-addresses-for-pml4-table lin-addr base-addr x86-1)
		  (translation-governing-addresses-for-pml4-table lin-addr base-addr x86-2)))
  :hints (("Goal" :in-theory (e/d* (translation-governing-addresses-for-pml4-table)
				   (xlate-equiv-memory-and-xlate-equiv-entries-rm-low-64-with-pml4-table-entry-addr))
	   :use ((:instance xlate-equiv-memory-and-xlate-equiv-entries-rm-low-64-with-pml4-table-entry-addr)
		 (:instance xlate-equiv-entries-and-page-size
			    (e-1 (rm-low-64 (pml4-table-entry-addr lin-addr base-addr) x86-1))
			    (e-2 (rm-low-64 (pml4-table-entry-addr lin-addr base-addr) x86-2))))))
  :rule-classes :congruence)

(defthm translation-governing-addresses-and-xlate-equiv-memory
  (implies (xlate-equiv-memory x86-1 x86-2)
	   (equal (translation-governing-addresses lin-addr x86-1)
		  (translation-governing-addresses lin-addr x86-2)))
  :hints (("Goal"
	   :in-theory (e/d* (translation-governing-addresses) ())
	   :use ((:instance xlate-equiv-memory-and-cr3))))
  :rule-classes :congruence)

(defthm all-translation-governing-addresses-and-xlate-equiv-memory
  (implies (xlate-equiv-memory x86-1 x86-2)
	   (equal (all-translation-governing-addresses lin-addr x86-1)
		  (all-translation-governing-addresses lin-addr x86-2)))
  :rule-classes :congruence)

;; ----------------------------------------------------------------------

;; Proof of
;; all-translation-governing-addresses-and-mv-nth-1-wb-disjoint and
;; translation-governing-addresses-and-mv-nth-1-wb-disjoint-p:

(defthm xr-mem-disjoint-ia32e-la-to-pa-page-table-in-marking-mode
  (implies (and (disjoint-p (list index)
			    (translation-governing-addresses-for-page-table
			     lin-addr base-addr (double-rewrite x86)))
		(canonical-address-p lin-addr)
		(physical-address-p base-addr)
		(equal (loghead 12 base-addr) 0))
	   (equal (xr :mem index (mv-nth 2 (ia32e-la-to-pa-page-table
					    lin-addr
					    base-addr u/s-acc r/w-acc x/d-acc
					    wp smep smap ac nxe r-w-x cpl x86)))
		  (xr :mem index x86)))
  :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa-page-table
				    translation-governing-addresses-for-page-table)
				   (negative-logand-to-positive-logand-with-integerp-x
				    bitops::logand-with-negated-bitmask)))))

(defthm xr-mem-disjoint-ia32e-la-to-pa-page-directory-in-marking-mode
  (implies (and (disjoint-p (list index)
			    (translation-governing-addresses-for-page-directory
			     lin-addr base-addr (double-rewrite x86)))
		(canonical-address-p lin-addr)
		(physical-address-p base-addr)
		(equal (loghead 12 base-addr) 0))
	   (equal (xr :mem index (mv-nth 2 (ia32e-la-to-pa-page-directory
					    lin-addr
					    base-addr u/s-acc r/w-acc x/d-acc
					    wp smep smap ac nxe r-w-x cpl x86)))
		  (xr :mem index x86)))
  :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa-page-directory
				    translation-governing-addresses-for-page-directory)
				   (negative-logand-to-positive-logand-with-integerp-x
				    bitops::logand-with-negated-bitmask)))))

(defthm xr-mem-disjoint-ia32e-la-to-pa-page-dir-ptr-table-in-marking-mode
  (implies (and (disjoint-p (list index)
			    (translation-governing-addresses-for-page-dir-ptr-table
			     lin-addr base-addr (double-rewrite x86)))
		(canonical-address-p lin-addr)
		(physical-address-p base-addr)
		(equal (loghead 12 base-addr) 0))
	   (equal (xr :mem index (mv-nth 2 (ia32e-la-to-pa-page-dir-ptr-table
					    lin-addr
					    base-addr u/s-acc r/w-acc x/d-acc
					    wp smep smap ac nxe r-w-x cpl x86)))
		  (xr :mem index x86)))
  :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa-page-dir-ptr-table
				    translation-governing-addresses-for-page-dir-ptr-table)
				   (negative-logand-to-positive-logand-with-integerp-x
				    bitops::logand-with-negated-bitmask)))))

(defthm xr-mem-disjoint-ia32e-la-to-pa-pml4-table-in-marking-mode
  (implies (and (disjoint-p (list index)
			    (translation-governing-addresses-for-pml4-table
			     lin-addr base-addr (double-rewrite x86)))
		(canonical-address-p lin-addr)
		(physical-address-p base-addr)
		(equal (loghead 12 base-addr) 0))
	   (equal (xr :mem index (mv-nth 2 (ia32e-la-to-pa-pml4-table
					    lin-addr base-addr
					    wp smep smap ac nxe r-w-x cpl x86)))
		  (xr :mem index x86)))
  :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa-pml4-table
				    translation-governing-addresses-for-pml4-table)
				   (negative-logand-to-positive-logand-with-integerp-x
				    bitops::logand-with-negated-bitmask)))))

(defthm xr-mem-disjoint-ia32e-la-to-pa-in-marking-mode
  (implies (and (disjoint-p (list index)
			    (translation-governing-addresses lin-addr (double-rewrite x86)))
		(canonical-address-p lin-addr))
	   (equal (xr :mem index (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x cpl x86)))
		  (xr :mem index x86)))
  :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa
				    translation-governing-addresses)
				   (negative-logand-to-positive-logand-with-integerp-x
				    bitops::logand-with-negated-bitmask
				    force (force))))))

(defthm rm-low-64-disjoint-ia32e-la-to-pa-in-marking-mode
  (implies (and (disjoint-p (addr-range 8 index)
			    (translation-governing-addresses lin-addr (double-rewrite x86)))
		(canonical-address-p lin-addr))
	   (equal (rm-low-64 index (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x cpl x86)))
		  (rm-low-64 index x86)))
  :hints (("Goal" :in-theory (e/d* (rm-low-64 rm-low-32 disjoint-p)
				   (translation-governing-addresses
				    negative-logand-to-positive-logand-with-integerp-x
				    bitops::logand-with-negated-bitmask
				    force (force))))))

;; For the proof of rm-low-64-disjoint-las-to-pas-in-marking-mode-disjoint:

;; (defthm translation-governing-addresses-for-page-table-and-mv-nth-2-ia32e-la-to-pa
;;   (equal (translation-governing-addresses-for-page-table
;;           lin-addr-1 base-addr-1 (mv-nth 2 (ia32e-la-to-pa lin-addr-2 r-w-x cpl x86)))
;;          (translation-governing-addresses-for-page-table
;;           lin-addr-1 base-addr-1 x86))
;;   :hints (("Goal" :in-theory (e/d* (translation-governing-addresses-for-page-table) ()))))

;; (defthm translation-governing-addresses-for-page-directory-and-mv-nth-2-ia32e-la-to-pa
;;   (implies (x86p x86)
;;            (equal (translation-governing-addresses-for-page-directory
;;                    lin-addr-1 base-addr-1 (mv-nth 2 (ia32e-la-to-pa lin-addr-2 r-w-x cpl x86)))
;;                   (translation-governing-addresses-for-page-directory
;;                    lin-addr-1 base-addr-1 x86)))
;;   :hints (("Goal"
;;            :use ((:instance xlate-equiv-memory-and-xlate-equiv-entries-rm-low-64-with-page-directory-entry-addr
;;                             (lin-addr lin-addr-1)
;;                             (base-addr base-addr-1)
;;                             (x86-1 (mv-nth 2 (ia32e-la-to-pa lin-addr-2 r-w-x cpl x86)))
;;                             (x86-2 x86))
;;                  (:instance xlate-equiv-entries-and-page-size
;;                             (e-1 (rm-low-64 (page-directory-entry-addr lin-addr-1 base-addr-1)
;;                                             (mv-nth 2 (ia32e-la-to-pa lin-addr-2 r-w-x cpl x86))))
;;                             (e-2 (rm-low-64 (page-directory-entry-addr lin-addr-1 base-addr-1)
;;                                             x86))))
;;            :in-theory (e/d* (translation-governing-addresses-for-page-directory
;;                              translation-governing-addresses
;;                              translation-governing-addresses-for-page-table
;;                              translation-governing-addresses-for-page-dir-ptr-table
;;                              translation-governing-addresses-for-pml4-table
;;                              disjoint-p
;;                              member-p)
;;                             (xlate-equiv-memory-and-xlate-equiv-entries-rm-low-64-with-page-directory-entry-addr)))))

;; (defthm translation-governing-addresses-for-page-dir-ptr-table-and-mv-nth-2-ia32e-la-to-pa
;;   (implies (x86p x86)
;;            (equal (translation-governing-addresses-for-page-dir-ptr-table
;;                    lin-addr-1 base-addr-1 (mv-nth 2 (ia32e-la-to-pa lin-addr-2 r-w-x cpl x86)))
;;                   (translation-governing-addresses-for-page-dir-ptr-table
;;                    lin-addr-1 base-addr-1 x86)))
;;   :hints (("Goal"
;;            :use ((:instance xlate-equiv-memory-and-xlate-equiv-entries-rm-low-64-with-page-dir-ptr-table-entry-addr
;;                             (lin-addr lin-addr-1)
;;                             (base-addr base-addr-1)
;;                             (x86-1 (mv-nth 2 (ia32e-la-to-pa lin-addr-2 r-w-x cpl x86)))
;;                             (x86-2 x86))
;;                  (:instance xlate-equiv-entries-and-page-size
;;                             (e-1 (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr-1 base-addr-1)
;;                                             (mv-nth 2 (ia32e-la-to-pa lin-addr-2 r-w-x cpl x86))))
;;                             (e-2 (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr-1 base-addr-1)
;;                                             x86))))
;;            :in-theory (e/d* (translation-governing-addresses-for-page-dir-ptr-table
;;                              translation-governing-addresses-for-pml4-table
;;                              translation-governing-addresses
;;                              disjoint-p
;;                              member-p)
;;                             (xlate-equiv-memory-and-xlate-equiv-entries-rm-low-64-with-page-dir-ptr-table-entry-addr)))))

;; (defthm translation-governing-addresses-for-pml4-table-and-mv-nth-2-ia32e-la-to-pa
;;   (implies (x86p x86)
;;            (equal (translation-governing-addresses-for-pml4-table
;;                    lin-addr-1 base-addr-1 (mv-nth 2 (ia32e-la-to-pa lin-addr-2 r-w-x cpl x86)))
;;                   (translation-governing-addresses-for-pml4-table
;;                    lin-addr-1 base-addr-1 x86)))
;;   :hints (("Goal"
;;            :use ((:instance xlate-equiv-memory-and-xlate-equiv-entries-rm-low-64-with-pml4-table-entry-addr
;;                             (lin-addr lin-addr-1)
;;                             (base-addr base-addr-1)
;;                             (x86-1 (mv-nth 2 (ia32e-la-to-pa lin-addr-2 r-w-x cpl x86)))
;;                             (x86-2 x86))
;;                  (:instance xlate-equiv-entries-and-page-size
;;                             (e-1 (rm-low-64 (pml4-table-entry-addr lin-addr-1 base-addr-1)
;;                                             (mv-nth 2 (ia32e-la-to-pa lin-addr-2 r-w-x cpl x86))))
;;                             (e-2 (rm-low-64 (pml4-table-entry-addr lin-addr-1 base-addr-1)
;;                                             x86))))
;;            :in-theory (e/d* (translation-governing-addresses-for-pml4-table
;;                              translation-governing-addresses
;;                              disjoint-p
;;                              member-p)
;;                             (xlate-equiv-memory-and-xlate-equiv-entries-rm-low-64-with-pml4-table-entry-addr)))))

;; (defthm translation-governing-addresses-and-mv-nth-2-ia32e-la-to-pa
;;   (implies (x86p x86)
;;            (equal (translation-governing-addresses
;;                    lin-addr-1 (mv-nth 2 (ia32e-la-to-pa lin-addr-2 r-w-x cpl x86)))
;;                   (translation-governing-addresses
;;                    lin-addr-1 x86)))
;;   :hints (("Goal" :in-theory (e/d* (translation-governing-addresses) ()))))

;; (defthm all-translation-governing-addresses-and-mv-nth-2-ia32e-la-to-pa
;;   (implies (x86p x86)
;;            (equal (all-translation-governing-addresses
;;                    l-addrs-1 (mv-nth 2 (ia32e-la-to-pa lin-addr-2 r-w-x cpl x86)))
;;                   (all-translation-governing-addresses
;;                    l-addrs-1 x86)))
;;   :hints (("Goal" :in-theory (e/d* (all-translation-governing-addresses) ()))))


(defthm rm-low-64-disjoint-las-to-pas-in-marking-mode-disjoint
  (implies (and (disjoint-p (addr-range 8 index)
			    (all-translation-governing-addresses l-addrs (double-rewrite x86)))
		(canonical-address-listp l-addrs)
		(x86p x86))
	   (equal (rm-low-64 index (mv-nth 2 (las-to-pas l-addrs r-w-x cpl x86)))
		  (rm-low-64 index x86)))
  :hints (("Goal" :induct (las-to-pas l-addrs r-w-x cpl x86)
	   :in-theory (e/d* (las-to-pas
			     disjoint-p)
			    (translation-governing-addresses
			     negative-logand-to-positive-logand-with-integerp-x
			     bitops::logand-with-negated-bitmask
			     force (force))))))

;; ----------------------------------------------------------------------

(defthm translation-governing-addresses-for-page-table-and-write-to-physical-memory
  (equal (translation-governing-addresses-for-page-table
	  lin-addr page-table-base-addr
	  (write-to-physical-memory p-addrs bytes x86))
	 (translation-governing-addresses-for-page-table
	  lin-addr page-table-base-addr (double-rewrite x86)))
  :hints (("Goal" :in-theory (e/d* (translation-governing-addresses-for-page-table)
				   ()))))

(defthm translation-governing-addresses-for-page-table-and-mv-nth-2-las-to-pas
  (equal (translation-governing-addresses-for-page-table
	  lin-addr page-table-base-addr
	  (mv-nth 2 (las-to-pas l-addrs r-w-x cpl x86)))
	 (translation-governing-addresses-for-page-table
	  lin-addr page-table-base-addr (double-rewrite x86)))
  :hints (("Goal" :in-theory (e/d* (translation-governing-addresses-for-page-table)
				   ()))))

(defthm translation-governing-addresses-for-page-table-and-mv-nth-1-wb
  (equal (translation-governing-addresses-for-page-table
	  lin-addr page-table-base-addr
	  (mv-nth 1 (wb addr-lst x86)))
	 (translation-governing-addresses-for-page-table
	  lin-addr page-table-base-addr (double-rewrite x86)))
  :hints (("Goal" :in-theory (e/d* (wb
				    translation-governing-addresses-for-page-table)
				   ()))))

;; ----------------------------------------------------------------------

(defthm translation-governing-addresses-for-page-directory-and-write-to-physical-memory-disjoint-p
  (implies (disjoint-p (translation-governing-addresses-for-page-directory
			lin-addr page-directory-base-addr (double-rewrite x86))
		       p-addrs)
	   (equal (translation-governing-addresses-for-page-directory
		   lin-addr page-directory-base-addr
		   (write-to-physical-memory p-addrs bytes x86))
		  (translation-governing-addresses-for-page-directory
		   lin-addr page-directory-base-addr (double-rewrite x86))))
  :hints (("Goal"
	   :do-not-induct t
	   :in-theory (e/d* (disjoint-p
			     translation-governing-addresses-for-page-directory)
			    ()))))

(defthm translation-governing-addresses-for-page-directory-and-mv-nth-2-las-to-pas
  (equal (translation-governing-addresses-for-page-directory
	  lin-addr page-directory-base-addr
	  (mv-nth 2 (las-to-pas l-addrs r-w-x cpl x86)))
	 (translation-governing-addresses-for-page-directory
	  lin-addr page-directory-base-addr (double-rewrite x86))))

(defthm translation-governing-addresses-for-page-directory-and-mv-nth-1-wb-disjoint-p
  (implies (and (disjoint-p
		 (translation-governing-addresses-for-page-directory
		  lin-addr page-directory-base-addr (double-rewrite x86))
		 (all-translation-governing-addresses (strip-cars addr-lst)
						      (double-rewrite x86)))
		(disjoint-p
		 (translation-governing-addresses-for-page-directory
		  lin-addr page-directory-base-addr (double-rewrite x86))
		 (mv-nth 1 (las-to-pas (strip-cars addr-lst)
				       :w
				       (cpl x86)
				       (double-rewrite x86))))
		(addr-byte-alistp addr-lst)
		(not (programmer-level-mode x86))
		(x86p x86))
	   (equal (translation-governing-addresses-for-page-directory
		   lin-addr page-directory-base-addr
		   (mv-nth 1 (wb addr-lst x86)))
		  (translation-governing-addresses-for-page-directory
		   lin-addr page-directory-base-addr (double-rewrite x86))))
  :hints (("Goal"
	   :do-not-induct t
	   :in-theory (e/d* (disjoint-p
			     wb
			     translation-governing-addresses-for-page-directory)
			    ()))))

;; ----------------------------------------------------------------------

(defthm translation-governing-addresses-for-page-dir-ptr-table-and-write-to-physical-memory-disjoint-p
  (implies (disjoint-p (translation-governing-addresses-for-page-dir-ptr-table
			lin-addr page-dir-ptr-table-base-addr (double-rewrite x86))
		       p-addrs)
	   (equal (translation-governing-addresses-for-page-dir-ptr-table
		   lin-addr page-dir-ptr-table-base-addr
		   (write-to-physical-memory p-addrs bytes x86))
		  (translation-governing-addresses-for-page-dir-ptr-table
		   lin-addr page-dir-ptr-table-base-addr (double-rewrite x86))))
  :hints (("Goal"
	   :do-not-induct t
	   :in-theory (e/d* (disjoint-p
			     translation-governing-addresses-for-page-dir-ptr-table)
			    ()))))

(defthm translation-governing-addresses-for-page-dir-ptr-table-and-mv-nth-2-las-to-pas-disjoint-p
  (equal (translation-governing-addresses-for-page-dir-ptr-table
	  lin-addr page-dir-ptr-table-base-addr
	  (mv-nth 2 (las-to-pas l-addrs r-w-x cpl x86)))
	 (translation-governing-addresses-for-page-dir-ptr-table
	  lin-addr page-dir-ptr-table-base-addr (double-rewrite x86))))

(defthm translation-governing-addresses-for-page-dir-ptr-table-and-mv-nth-1-wb-disjoint-p
  (implies (and (disjoint-p
		 (translation-governing-addresses-for-page-dir-ptr-table
		  lin-addr page-dir-ptr-table-base-addr (double-rewrite x86))
		 (all-translation-governing-addresses (strip-cars addr-lst)
						      (double-rewrite x86)))
		(disjoint-p
		 (translation-governing-addresses-for-page-dir-ptr-table
		  lin-addr page-dir-ptr-table-base-addr (double-rewrite x86))
		 (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w (cpl x86)
				       (double-rewrite x86))))
		(addr-byte-alistp addr-lst)
		(not (programmer-level-mode x86))
		(x86p x86))
	   (equal (translation-governing-addresses-for-page-dir-ptr-table
		   lin-addr page-dir-ptr-table-base-addr
		   (mv-nth 1 (wb addr-lst x86)))
		  (translation-governing-addresses-for-page-dir-ptr-table
		   lin-addr page-dir-ptr-table-base-addr (double-rewrite x86))))
  :hints (("Goal"
	   :do-not-induct t
	   :in-theory (e/d* (disjoint-p
			     disjoint-p-commutative
			     wb
			     translation-governing-addresses-for-page-dir-ptr-table)
			    ()))))

;; ----------------------------------------------------------------------

(defthm translation-governing-addresses-for-pml4-table-and-write-to-physical-memory-disjoint-p
  (implies (disjoint-p (translation-governing-addresses-for-pml4-table
			lin-addr pml4-table-base-addr (double-rewrite x86))
		       p-addrs)
	   (equal (translation-governing-addresses-for-pml4-table
		   lin-addr pml4-table-base-addr
		   (write-to-physical-memory p-addrs bytes x86))
		  (translation-governing-addresses-for-pml4-table
		   lin-addr pml4-table-base-addr (double-rewrite x86))))
  :hints (("Goal"
	   :do-not-induct t
	   :in-theory (e/d* (disjoint-p
			     disjoint-p-commutative
			     translation-governing-addresses-for-pml4-table)
			    ()))))

(defthm translation-governing-addresses-for-pml4-table-and-mv-nth-2-las-to-pas-disjoint-p
  (equal (translation-governing-addresses-for-pml4-table
	  lin-addr pml4-table-base-addr
	  (mv-nth 2 (las-to-pas l-addrs r-w-x cpl x86)))
	 (translation-governing-addresses-for-pml4-table
	  lin-addr pml4-table-base-addr (double-rewrite x86))))

(defthm translation-governing-addresses-for-pml4-table-and-mv-nth-1-wb-disjoint-p
  (implies (and (disjoint-p
		 (translation-governing-addresses-for-pml4-table
		  lin-addr pml4-table-base-addr (double-rewrite x86))
		 (all-translation-governing-addresses (strip-cars addr-lst) (double-rewrite x86)))
		(disjoint-p
		 (translation-governing-addresses-for-pml4-table
		  lin-addr pml4-table-base-addr (double-rewrite x86))
		 (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w (cpl x86)
				       (double-rewrite x86))))
		(not (programmer-level-mode x86))
		(addr-byte-alistp addr-lst)
		(x86p x86))
	   (equal (translation-governing-addresses-for-pml4-table
		   lin-addr pml4-table-base-addr
		   (mv-nth 1 (wb addr-lst x86)))
		  (translation-governing-addresses-for-pml4-table
		   lin-addr pml4-table-base-addr (double-rewrite x86))))
  :hints (("Goal"
	   :do-not-induct t
	   :in-theory (e/d* (disjoint-p
			     wb
			     translation-governing-addresses-for-pml4-table)
			    (force (force))))))

;; ----------------------------------------------------------------------

(defthm translation-governing-addresses-and-write-to-physical-memory-disjoint-p
  (implies (disjoint-p (translation-governing-addresses lin-addr (double-rewrite x86))
		       p-addrs)
	   (equal (translation-governing-addresses
		   lin-addr (write-to-physical-memory p-addrs bytes x86))
		  (translation-governing-addresses lin-addr (double-rewrite x86))))
  :hints (("Goal"
	   :do-not-induct t
	   :in-theory (e/d* (disjoint-p translation-governing-addresses) ()))))

(defthm translation-governing-addresses-and-mv-nth-2-las-to-pas-disjoint-p
  (equal (translation-governing-addresses
	  lin-addr (mv-nth 2 (las-to-pas l-addrs r-w-x cpl x86)))
	 (translation-governing-addresses lin-addr (double-rewrite x86))))

(defthm translation-governing-addresses-and-mv-nth-1-wb-disjoint-p
  (implies (and
	    (disjoint-p (translation-governing-addresses lin-addr (double-rewrite x86))
			(all-translation-governing-addresses
			 (strip-cars addr-lst) (double-rewrite x86)))
	    (disjoint-p (translation-governing-addresses lin-addr (double-rewrite x86))
			(mv-nth 1 (las-to-pas (strip-cars addr-lst) :w (cpl x86)
					      (double-rewrite x86))))
	    (not (programmer-level-mode x86))
	    (addr-byte-alistp addr-lst)
	    (x86p x86))
	   (equal (translation-governing-addresses lin-addr (mv-nth 1 (wb addr-lst x86)))
		  (translation-governing-addresses lin-addr (double-rewrite x86))))
  :hints (("Goal"
	   :do-not-induct t
	   :in-theory (e/d* (disjoint-p
			     translation-governing-addresses)
			    (wb)))))

(defthm all-translation-governing-addresses-and-write-to-physical-memory-disjoint-p
  (implies (and (disjoint-p (all-translation-governing-addresses l-addrs (double-rewrite x86))
			    p-addrs)
		(physical-address-listp p-addrs)
		(byte-listp bytes)
		(equal (len p-addrs) (len bytes)))
	   (equal (all-translation-governing-addresses
		   l-addrs (write-to-physical-memory p-addrs bytes x86))
		  (all-translation-governing-addresses l-addrs (double-rewrite x86))))
  :hints (("Goal"
	   :in-theory (e/d* (disjoint-p
			     disjoint-p-commutative
			     all-translation-governing-addresses)
			    ()))))

(defthm all-translation-governing-addresses-and-mv-nth-2-las-to-pas
  (equal (all-translation-governing-addresses
	  l-addrs-1 (mv-nth 2 (las-to-pas l-addrs-2 r-w-x cpl x86)))
	 (all-translation-governing-addresses l-addrs-1 (double-rewrite x86)))
  :hints (("Goal"
	   :in-theory (e/d* (disjoint-p all-translation-governing-addresses) ()))))

(defthm all-translation-governing-addresses-and-mv-nth-1-wb-disjoint
  (implies (and
	    (disjoint-p (all-translation-governing-addresses l-addrs (double-rewrite x86))
			(all-translation-governing-addresses (strip-cars addr-lst) (double-rewrite x86)))
	    (disjoint-p (all-translation-governing-addresses l-addrs (double-rewrite x86))
			(mv-nth 1 (las-to-pas (strip-cars addr-lst) :w (cpl x86) (double-rewrite x86))))
	    (not (programmer-level-mode x86))
	    (addr-byte-alistp addr-lst)
	    (x86p x86))
	   (equal (all-translation-governing-addresses l-addrs (mv-nth 1 (wb addr-lst x86)))
		  (all-translation-governing-addresses l-addrs (double-rewrite x86))))
  :hints (("Goal"
	   :in-theory (e/d* (all-translation-governing-addresses)
			    (translation-governing-addresses
			     wb))
	   :induct (all-translation-governing-addresses l-addrs x86))))

(defthm translation-governing-addresses-and-write-to-physical-memory
  (implies (and (disjoint-p p-addrs (all-translation-governing-addresses l-addrs (double-rewrite x86)))
		(physical-address-listp p-addrs)
		(byte-listp bytes)
		(equal (len p-addrs) (len bytes)))
	   (equal
	    (all-translation-governing-addresses l-addrs (write-to-physical-memory p-addrs bytes x86))
	    (all-translation-governing-addresses l-addrs (double-rewrite x86))))
  :hints (("Goal" :in-theory (e/d* (disjoint-p-commutative) ()))))

;; ======================================================================

(defthm mv-nth-0-ia32e-la-to-pa-member-of-mv-nth-1-las-to-pas-if-lin-addr-member-p
  (implies (and (bind-free (find-l-addrs-from-las-to-pas 'l-addrs mfc state)
			   (l-addrs))
		(member-p lin-addr l-addrs)
		(not (mv-nth 0 (las-to-pas l-addrs r-w-x cpl x86))))
	   (equal (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x cpl x86)) nil))
  :hints (("Goal" :in-theory (e/d* (member-p) ()))))

(defthm mv-nth-1-ia32e-la-to-pa-member-of-mv-nth-1-las-to-pas-if-lin-addr-member-p
  (implies (and (member-p lin-addr l-addrs)
		(not (mv-nth 0 (las-to-pas l-addrs r-w-x cpl x86))))
	   (member-p (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x cpl x86))
		     (mv-nth 1 (las-to-pas     l-addrs r-w-x cpl x86))))
  :hints (("Goal" :in-theory (e/d* (member-p) ()))))

(defthm mv-nth-0-las-to-pas-after-mv-nth-2-ia32e-la-to-pa
  ;; (:CONGRUENCE XLATE-EQUIV-MEMORY-AND-MV-NTH-0-LAS-TO-PAS)
  ;; (:REWRITE XLATE-EQUIV-MEMORY-WITH-MV-NTH-2-IA32E-LA-TO-PA)
  (equal (mv-nth 0 (las-to-pas l-addrs-1 r-w-x-1 cpl-1
			       (mv-nth 2 (ia32e-la-to-pa lin-addr-2 r-w-x-2 cpl-2 x86))))
	 (mv-nth 0 (las-to-pas l-addrs-1 r-w-x-1 cpl-1 x86))))

(defthm mv-nth-1-las-to-pas-after-mv-nth-2-ia32e-la-to-pa
  ;; (:CONGRUENCE XLATE-EQUIV-MEMORY-AND-MV-NTH-1-LAS-TO-PAS)
  ;; (:REWRITE XLATE-EQUIV-MEMORY-WITH-MV-NTH-2-IA32E-LA-TO-PA)
  (equal (mv-nth 1 (las-to-pas l-addrs-1 r-w-x-1 cpl-1
			       (mv-nth 2 (ia32e-la-to-pa lin-addr-2 r-w-x-2 cpl-2 x86))))
	 (mv-nth 1 (las-to-pas l-addrs-1 r-w-x-1 cpl-1 x86))))

(defthmd open-mv-nth-0-las-to-pas
  (implies (and (canonical-address-p lin-addr)
		(not (zp n)))
	   (equal (mv-nth 0 (las-to-pas (create-canonical-address-list n lin-addr) r-w-x cpl x86))
		  (if (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x cpl x86))
		      (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x cpl x86))
		    (mv-nth 0 (las-to-pas (create-canonical-address-list (+ -1 n) (+ 1 lin-addr))
					  r-w-x cpl x86))))))

(defthmd open-mv-nth-1-las-to-pas
  (implies (and (canonical-address-p lin-addr)
		(not (zp n))
		(not (mv-nth 0 (las-to-pas (create-canonical-address-list n lin-addr) r-w-x cpl x86))))
	   (equal (mv-nth 1 (las-to-pas (create-canonical-address-list n lin-addr) r-w-x cpl x86))
		  (cons (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x cpl x86))
			(mv-nth 1 (las-to-pas (create-canonical-address-list (+ -1 n) (+ 1 lin-addr))
					      r-w-x cpl x86))))))

;; ======================================================================

(defthm xw-mem-and-ia32e-la-to-pa-page-table-commute
  (implies (and
	    (disjoint-p
	     (list index)
	     (translation-governing-addresses-for-page-table lin-addr base-addr (double-rewrite x86)))
	    (canonical-address-p lin-addr)
	    (physical-address-p base-addr)
	    (equal (loghead 12 base-addr) 0))
	   (equal (xw :mem index value (mv-nth 2 (ia32e-la-to-pa-page-table
						  lin-addr
						  base-addr u/s-acc r/w-acc x/d-acc
						  wp smep smap ac nxe r-w-x cpl x86)))
		  (mv-nth 2 (ia32e-la-to-pa-page-table
			     lin-addr
			     base-addr u/s-acc r/w-acc x/d-acc
			     wp smep smap ac nxe r-w-x cpl
			     (xw :mem index value x86)))))
  :hints (("Goal" :in-theory (e/d* (disjoint-p
				    translation-governing-addresses-for-page-table
				    ia32e-la-to-pa-page-table)
				   (bitops::logand-with-negated-bitmask)))))

(defthm xw-mem-and-ia32e-la-to-pa-page-directory-commute
  (implies (and
	    (disjoint-p
	     (list index)
	     (translation-governing-addresses-for-page-directory lin-addr base-addr (double-rewrite x86)))
	    (canonical-address-p lin-addr)
	    (physical-address-p base-addr)
	    (equal (loghead 12 base-addr) 0)
	    (integerp index))
	   (equal (xw :mem index value (mv-nth 2 (ia32e-la-to-pa-page-directory
						  lin-addr
						  base-addr u/s-acc r/w-acc x/d-acc
						  wp smep smap ac nxe r-w-x cpl x86)))
		  (mv-nth 2 (ia32e-la-to-pa-page-directory
			     lin-addr
			     base-addr u/s-acc r/w-acc x/d-acc
			     wp smep smap ac nxe r-w-x cpl
			     (xw :mem index value x86)))))
  :hints (("Goal" :in-theory (e/d* (disjoint-p
				    translation-governing-addresses-for-page-directory
				    ia32e-la-to-pa-page-directory)
				   (bitops::logand-with-negated-bitmask
				    |(xw :mem addr1 (wm-low-64 addr2 val x86)) --- disjoint addr|)))))

(defthm xw-mem-and-ia32e-la-to-pa-page-dir-ptr-table-commute
  (implies (and
	    (disjoint-p
	     (list index)
	     (translation-governing-addresses-for-page-dir-ptr-table lin-addr base-addr (double-rewrite x86)))
	    (canonical-address-p lin-addr)
	    (physical-address-p base-addr)
	    (equal (loghead 12 base-addr) 0)
	    (integerp index))
	   (equal (xw :mem index value (mv-nth 2 (ia32e-la-to-pa-page-dir-ptr-table
						  lin-addr
						  base-addr u/s-acc r/w-acc x/d-acc
						  wp smep smap ac nxe r-w-x cpl x86)))
		  (mv-nth 2 (ia32e-la-to-pa-page-dir-ptr-table
			     lin-addr
			     base-addr u/s-acc r/w-acc x/d-acc
			     wp smep smap ac nxe r-w-x cpl
			     (xw :mem index value x86)))))
  :hints (("Goal" :in-theory (e/d* (disjoint-p
				    translation-governing-addresses-for-page-dir-ptr-table
				    ia32e-la-to-pa-page-dir-ptr-table)
				   (|(xw :mem addr1 (wm-low-64 addr2 val x86)) --- disjoint addr|
				    bitops::logand-with-negated-bitmask)))))

(defthm xw-mem-and-ia32e-la-to-pa-pml4-table-commute
  (implies (and
	    (disjoint-p
	     (list index)
	     (translation-governing-addresses-for-pml4-table lin-addr base-addr (double-rewrite x86)))
	    (canonical-address-p lin-addr)
	    (physical-address-p base-addr)
	    (equal (loghead 12 base-addr) 0)
	    (integerp index))
	   (equal (xw :mem index value (mv-nth 2 (ia32e-la-to-pa-pml4-table
						  lin-addr base-addr
						  wp smep smap ac nxe r-w-x cpl x86)))
		  (mv-nth 2 (ia32e-la-to-pa-pml4-table
			     lin-addr base-addr
			     wp smep smap ac nxe r-w-x cpl
			     (xw :mem index value x86)))))
  :hints (("Goal" :in-theory (e/d* (disjoint-p
				    translation-governing-addresses-for-pml4-table
				    ia32e-la-to-pa-pml4-table)
				   (|(xw :mem addr1 (wm-low-64 addr2 val x86)) --- disjoint addr|
				    bitops::logand-with-negated-bitmask)))))

(defthm xw-mem-and-ia32e-la-to-pa-commute
  (implies (and (disjoint-p
		 (list index)
		 (translation-governing-addresses lin-addr (double-rewrite x86)))
		(canonical-address-p lin-addr)
		(integerp index))
	   (equal (xw :mem index value (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x cpl x86)))
		  (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x cpl (xw :mem index value x86)))))
  :hints (("Goal" :in-theory (e/d* (disjoint-p translation-governing-addresses ia32e-la-to-pa)
				   ()))))

(defthm write-to-physical-memory-and-mv-nth-2-ia32e-la-to-pa-commute
  (implies (and (disjoint-p
		 p-addrs
		 (translation-governing-addresses lin-addr (double-rewrite x86)))
		(canonical-address-p lin-addr)
		(physical-address-listp p-addrs)
		(byte-listp bytes)
		(equal (len bytes) (len p-addrs)))
	   (equal (write-to-physical-memory
		   p-addrs bytes (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x cpl x86)))
		  (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x cpl
					    (write-to-physical-memory p-addrs bytes x86)))))
  :hints (("Goal"
	   :induct (write-to-physical-memory p-addrs bytes x86)
	   :in-theory (e/d* (disjoint-p) ()))))

;; ======================================================================

(defthm las-to-pas-values-and-xw-mem-not-member
  (implies (and (not (member-p index (all-translation-governing-addresses l-addrs (double-rewrite x86))))
		(physical-address-p index)
		(canonical-address-listp l-addrs))
	   (and (equal (mv-nth 0 (las-to-pas l-addrs r-w-x cpl (xw :mem index byte x86)))
		       (mv-nth 0 (las-to-pas l-addrs r-w-x cpl x86)))
		(equal (mv-nth 1 (las-to-pas l-addrs r-w-x cpl (xw :mem index byte x86)))
		       (mv-nth 1 (las-to-pas l-addrs r-w-x cpl x86)))))
  :hints (("Goal"
	   :in-theory (e/d* (open-mv-nth-0-las-to-pas
			     open-mv-nth-1-las-to-pas
			     disjoint-p
			     member-p)
			    (translation-governing-addresses)))))

(defthmd las-to-pas-subset-p
  ;; This is a pretty expensive rule --- a more general version of
  ;; las-to-pas-subset-p-with-l-addrs-from-bind-free.
  (implies (and (bind-free (find-l-addrs-from-fn 'las-to-pas
						 'l-addrs
						 mfc state)
			   (l-addrs))
		(syntaxp (not (eq l-addrs-subset l-addrs)))
		(subset-p l-addrs-subset l-addrs)
		(not (mv-nth 0 (las-to-pas l-addrs r-w-x cpl x86))))
	   (equal (mv-nth 0 (las-to-pas l-addrs-subset r-w-x cpl x86))
		  nil))
  :hints (("Goal" :in-theory (e/d* (subset-p) ()))))

(defthm las-to-pas-subset-p-with-l-addrs-from-bind-free
  ;; This rule will help in fetching instructions.
  (implies (and (bind-free
		 (find-l-addrs-from-fn 'program-at 'l-addrs mfc state)
		 (l-addrs))
		(syntaxp (not (eq l-addrs-subset l-addrs)))
		(not (mv-nth 0 (las-to-pas l-addrs r-w-x cpl x86)))
		(subset-p l-addrs-subset l-addrs))
	   (equal (mv-nth 0 (las-to-pas l-addrs-subset r-w-x cpl x86))
		  nil))
  :hints (("Goal" :in-theory (e/d* (subset-p) ()))))

;; ======================================================================
