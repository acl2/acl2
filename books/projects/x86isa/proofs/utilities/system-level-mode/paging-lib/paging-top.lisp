;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")
(include-book "pml4-table-lemmas" :ttags :all)
(include-book "gather-paging-structures-thms" :ttags :all)

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))

(local (in-theory (e/d () (unsigned-byte-p signed-byte-p))))

;; ======================================================================

(local
 (defthmd xlate-equiv-memory-and-cr0
   (implies (and (xlate-equiv-memory x86-1 x86-2)
                 (not (programmer-level-mode x86-2)))
            (equal (bool->bit (logbitp 16 (xr :ctr *cr0* x86-1)))
                   (bool->bit (logbitp 16 (xr :ctr *cr0* x86-2)))))
   :hints (("Goal" :in-theory (e/d* (xlate-equiv-memory xlate-equiv-structures)
                                    ())))))

(local
 (defthmd xlate-equiv-memory-and-cr3
   (implies (and (xlate-equiv-memory x86-1 x86-2)
                 (not (programmer-level-mode x86-2)))
            (equal (loghead 40 (logtail 12 (xr :ctr *cr3* x86-1)))
                   (loghead 40 (logtail 12 (xr :ctr *cr3* x86-2)))))
   :hints (("Goal" :in-theory (e/d* (xlate-equiv-memory xlate-equiv-structures)
                                    ())))))

(local
 (defthmd xlate-equiv-memory-and-cr4
   (implies (and (xlate-equiv-memory x86-1 x86-2)
                 (not (programmer-level-mode x86-2)))
            (equal (bool->bit (logbitp 20 (xr :ctr *cr4* x86-1)))
                   (bool->bit (logbitp 20 (xr :ctr *cr4* x86-2)))))
   :hints (("Goal" :in-theory (e/d* (xlate-equiv-memory xlate-equiv-structures)
                                    ())))))

(local
 (defthmd xlate-equiv-memory-and-msr
   (implies (and (xlate-equiv-memory x86-1 x86-2)
                 (not (programmer-level-mode x86-2)))
            (equal (bool->bit (logbitp 11 (xr :msr *ia32_efer-idx* x86-1)))
                   (bool->bit (logbitp 11 (xr :msr *ia32_efer-idx* x86-2)))))
   :hints (("Goal" :in-theory (e/d* (xlate-equiv-memory xlate-equiv-structures)
                                    ())))))

(local
 (defthmd xlate-equiv-memory-and-rflags
   (implies (and (xlate-equiv-memory x86-1 x86-2)
                 (not (programmer-level-mode x86-2)))
            (equal (bool->bit (logbitp 18 (xr :rflags 0 x86-1)))
                   (bool->bit (logbitp 18 (xr :rflags 0 x86-2)))))
   :hints (("Goal" :in-theory (e/d* (xlate-equiv-memory xlate-equiv-structures)
                                    ())))))

;; ======================================================================

;; Lemmas about ia32e-la-to-pa:

(defthmd xlate-equiv-memory-and-ia32e-la-to-pa
  (implies (xlate-equiv-memory (double-rewrite x86-1) x86-2)
           (and
            (equal (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x cpl x86-1))
                   (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x cpl x86-2)))
            (equal (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x cpl x86-1))
                   (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x cpl x86-2)))))
  :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa) ())
           :use ((:instance xlate-equiv-memory-and-rflags)
                 (:instance xlate-equiv-memory-and-msr)
                 (:instance xlate-equiv-memory-and-cr0)
                 (:instance xlate-equiv-memory-and-cr3)
                 (:instance xlate-equiv-memory-and-cr4)))))

(defthm xlate-equiv-memory-and-mv-nth-0-ia32e-la-to-pa
  (implies (xlate-equiv-memory x86-1 x86-2)
           (equal (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x cpl x86-1))
                  (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x cpl x86-2))))
  :hints (("Goal" :use ((:instance xlate-equiv-memory-and-ia32e-la-to-pa))))
  :rule-classes :congruence)

(defthm xlate-equiv-memory-and-mv-nth-1-ia32e-la-to-pa
  (implies (xlate-equiv-memory x86-1 x86-2)
           (equal (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x cpl x86-1))
                  (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x cpl x86-2))))
  :hints (("Goal" :use ((:instance xlate-equiv-memory-and-ia32e-la-to-pa))))
  :rule-classes :congruence)

(defthm xlate-equiv-structures-and-mv-nth-2-ia32e-la-to-pa
  (implies
   (x86p x86)
   (xlate-equiv-structures (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x cpl x86))
                           (double-rewrite x86)))
  :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa) ()))))

(defthmd xlate-equiv-structures-and-two-mv-nth-2-ia32e-la-to-pa
  (implies
   (and (x86p x86-1)
        (x86p x86-2)
        (xlate-equiv-structures x86-1 x86-2))
   (xlate-equiv-structures (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x cpl x86-1))
                           (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x cpl x86-2)))))

(defthm all-mem-except-paging-structures-equal-with-mv-nth-2-ia32e-la-to-pa
  (implies
   (x86p x86)
   (all-mem-except-paging-structures-equal
    (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x cpl x86))
    (double-rewrite x86)))
  :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa
                                    ia32e-la-to-pa-pml4-table)
                                   (bitops::logand-with-negated-bitmask
                                    accessed-bit
                                    dirty-bit
                                    not)))))

(defthmd all-mem-except-paging-structures-equal-with-two-mv-nth-2-ia32e-la-to-pa
  (implies
   (and (x86p x86-1)
        (x86p x86-2)
        (all-mem-except-paging-structures-equal x86-1 x86-2))
   (all-mem-except-paging-structures-equal
    (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x cpl x86-1))
    (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x cpl x86-2)))))

(defthm xlate-equiv-memory-with-mv-nth-2-ia32e-la-to-pa
  (implies (x86p x86)
           (xlate-equiv-memory
            (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x cpl x86))
            (double-rewrite x86)))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (e/d* (xlate-equiv-memory)
                            (bitops::logand-with-negated-bitmask
                             accessed-bit
                             dirty-bit
                             not)))))

(defthmd xlate-equiv-memory-with-two-mv-nth-2-ia32e-la-to-pa
  (implies (and (x86p x86-1)
                (x86p x86-2)
                (xlate-equiv-memory x86-1 x86-2))
           (xlate-equiv-memory
            (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x cpl x86-1))
            (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x cpl x86-2)))))

(defthm two-page-walks-ia32e-la-to-pa
  (implies
   (x86p x86)
   (and

    (equal
     (mv-nth 0 (ia32e-la-to-pa lin-addr-1 r-w-x-1 cpl-1
                               (mv-nth 2 (ia32e-la-to-pa lin-addr-2 r-w-x-2 cpl-2 x86))))
     (mv-nth 0 (ia32e-la-to-pa lin-addr-1 r-w-x-1 cpl-1 x86)))

    (equal
     (mv-nth 1 (ia32e-la-to-pa lin-addr-1 r-w-x-1 cpl-1
                               (mv-nth 2 (ia32e-la-to-pa lin-addr-2 r-w-x-2 cpl-2 x86))))
     (mv-nth 1 (ia32e-la-to-pa lin-addr-1 r-w-x-1 cpl-1 x86)))))

  :hints (("Goal" :in-theory (e/d* () (ia32e-la-to-pa)))))

(in-theory (e/d* () (ia32e-la-to-pa)))

;; ======================================================================

(defthm gather-all-paging-structure-qword-addresses-mv-nth-2-ia32e-la-to-pa
  (implies (and (x86p x86)
                (not (programmer-level-mode x86)))
           (equal (gather-all-paging-structure-qword-addresses
                   (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x cpl x86)))
                  (gather-all-paging-structure-qword-addresses x86)))
  :hints (("Goal"
           :use ((:instance
                  gather-all-paging-structure-qword-addresses-with-xlate-equiv-structures
                  (x86-equiv (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x cpl x86))))))))


(defthm xlate-equiv-entries-at-qword-addresses-mv-nth-2-ia32e-la-to-pa
  (implies (and (equal addrs (gather-all-paging-structure-qword-addresses x86))
                (x86p x86)
                (not (programmer-level-mode x86)))
           (equal (xlate-equiv-entries-at-qword-addresses
                   addrs addrs
                   x86
                   (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x cpl x86)))
                  (xlate-equiv-entries-at-qword-addresses addrs addrs x86 x86)))
  :hints (("Goal" :in-theory (e/d* ()
                                   (xlate-equiv-structures-and-xlate-equiv-entries-at-qword-addresses
                                    booleanp-of-xlate-equiv-entries-at-qword-addresses))
           :use ((:instance xlate-equiv-structures-and-xlate-equiv-entries-at-qword-addresses
                            (addrs (gather-all-paging-structure-qword-addresses x86))
                            (x86 x86)
                            (x86-equiv (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x cpl x86))))
                 (:instance booleanp-of-xlate-equiv-entries-at-qword-addresses
                            (addrs (gather-all-paging-structure-qword-addresses x86))
                            (x x86)
                            (y x86))
                 (:instance booleanp-of-xlate-equiv-entries-at-qword-addresses
                            (addrs (gather-all-paging-structure-qword-addresses x86))
                            (x x86)
                            (y (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x cpl x86))))))))

;; ======================================================================

;; Lemmas about las-to-pas:

(defthmd xlate-equiv-memory-and-las-to-pas
  (implies (and (xlate-equiv-memory (double-rewrite x86-1) x86-2)
                (x86p x86-1)
                (x86p x86-2))
           (and
            (equal (mv-nth 0 (las-to-pas l-addrs r-w-x cpl x86-1))
                   (mv-nth 0 (las-to-pas l-addrs r-w-x cpl x86-2)))
            (equal (mv-nth 1 (las-to-pas l-addrs r-w-x cpl x86-1))
                   (mv-nth 1 (las-to-pas l-addrs r-w-x cpl x86-2)))))
  :hints (("Goal"
           :induct (cons (las-to-pas l-addrs r-w-x cpl x86-1)
                         (las-to-pas l-addrs r-w-x cpl x86-2)))))

(defthm xlate-equiv-memory-with-mv-nth-2-las-to-pas
  (implies (x86p x86)
           (xlate-equiv-memory
            (mv-nth 2 (las-to-pas l-addrs r-w-x cpl x86))
            (double-rewrite x86)))
  :hints (("Goal" :induct (las-to-pas l-addrs r-w-x cpl x86))))

(defthmd xlate-equiv-memory-with-two-mv-nth-2-las-to-pas
  (implies (and (x86p x86-1)
                (x86p x86-2)
                (xlate-equiv-memory x86-1 x86-2))
           (xlate-equiv-memory
            (mv-nth 2 (las-to-pas l-addrs r-w-x cpl x86-1))
            (mv-nth 2 (las-to-pas l-addrs r-w-x cpl x86-2))))
  :hints (("Goal"
           :induct (cons (las-to-pas l-addrs r-w-x cpl x86-1)
                         (las-to-pas l-addrs r-w-x cpl x86-2)))))

;; ======================================================================
