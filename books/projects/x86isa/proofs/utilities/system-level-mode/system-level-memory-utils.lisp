;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")
(include-book "paging-lib/paging-top")

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "centaur/gl/gl" :dir :system))

;; ======================================================================

(defsection system-level-memory-utils
  :parents (proof-utilities)

  :short "Helper lemmas for reasoning about memory in the system-level
  mode"
  )

(local (xdoc::set-default-parents system-level-memory-utils))

(local (in-theory (e/d* (entry-found-p-and-good-paging-structures-x86p
                         entry-found-p-and-lin-addr
                         ia32e-la-to-pa-and-ia32e-entries-found-la-to-pa)
                        (signed-byte-p
                         unsigned-byte-p))))

;; ======================================================================

(local
 (defthm cpl-unaffected-by-rm08
   (equal (xr :seg-visible 1 (mv-nth 2 (rm08 lin-addr r-w-x x86)))
          (xr :seg-visible 1 x86))
   :hints (("Goal" :in-theory (e/d* (rm08) (force (force)))))))

(local
 (defthm cpl-unaffected-by-wm08
   (equal (xr :seg-visible 1 (mv-nth 1 (wm08 addr byte x86)))
          (xr :seg-visible 1 x86))
   :hints (("Goal" :in-theory (e/d* (wm08) (force (force)))))))

(defthm good-paging-structures-x86p-and-mv-nth-2-ia32e-entries-found-la-to-pa
  (implies (good-paging-structures-x86p (double-rewrite x86))
           (good-paging-structures-x86p
            (mv-nth 2 (ia32e-entries-found-la-to-pa lin-addr r-w-x cpl x86))))
  :hints (("Goal" :in-theory (e/d* (good-paging-structures-x86p) ()))))

(defthmd xlate-equiv-x86s-open-for-cpl
  (implies (and (xlate-equiv-x86s x86-1 x86-2)
                (good-paging-structures-x86p x86-1))
           (equal (loghead 2 (xr :seg-visible 1 x86-1))
                  (loghead 2 (xr :seg-visible 1 x86-2))))
  :hints (("Goal" :in-theory (e/d* (xlate-equiv-x86s
                                    all-seg-visibles-equal)
                                   ()))))

(defthmd xlate-equiv-structures-open-for-cpl
  (implies (and (xlate-equiv-structures x86-1 x86-2)
                (good-paging-structures-x86p x86-1))
           (equal (loghead 2 (xr :seg-visible 1 x86-1))
                  (loghead 2 (xr :seg-visible 1 x86-2))))
  :hints (("Goal" :in-theory (e/d* (xlate-equiv-structures
                                    all-seg-visibles-equal)
                                   ()))))

(local
 (defthm open-create-canonical-address-list
   (implies (and (canonical-address-p lin-addr)
                 (posp n)
                 (canonical-address-p (+ -1 n lin-addr)))
            (equal (create-canonical-address-list n lin-addr)
                   (cons lin-addr
                         (create-canonical-address-list (+ -1 n) (+ 1 lin-addr)))))
   :hints (("Goal" :in-theory (e/d* () (signed-byte-p))))))

(defthmd create-canonical-address-list-end-addr-is-canonical
  (implies (and (equal (len (create-canonical-address-list count addr)) count)
                (posp count)
                (equal end-addr (+ -1 addr count)))
           (canonical-address-p end-addr)))

;; ======================================================================

(defthm rm08-values-and-xlate-equiv-x86s-disjoint
  ;; Here, we need xlate-equiv-x86s instead of merely
  ;; xlate-equiv-structures because we need to account for the
  ;; equality of all memory locations, apart from those that contain
  ;; the paging structures.
  (implies (and
            (bind-free
             (find-an-xlate-equiv-x86
              'rm08-values-and-xlate-equiv-x86s-disjoint
              'x86-2 x86-1)
             (x86-2))
            (paging-entries-found-p lin-addr (double-rewrite x86-1))
            (xlate-equiv-x86s (double-rewrite x86-1) x86-2)
            (pairwise-disjoint-p-aux
             ;; The read is not being done from the paging structures.
             (list
              (mv-nth
               1
               (ia32e-entries-found-la-to-pa
                lin-addr r-w-x (loghead 2 (xr :seg-visible 1 x86-1)) x86-1)))
             (open-qword-paddr-list-list
              (gather-all-paging-structure-qword-addresses x86-1))))
           (and (equal
                 (mv-nth 0 (rm08 lin-addr r-w-x x86-1))
                 (mv-nth 0 (rm08 lin-addr r-w-x x86-2)))
                (equal
                 (mv-nth 1 (rm08 lin-addr r-w-x x86-1))
                 (mv-nth 1 (rm08 lin-addr r-w-x x86-2)))))
  :hints (("Goal"
           :use ((:instance xlate-equiv-x86s-open-for-cpl)
                 (:instance gather-all-paging-structure-qword-addresses-with-xlate-equiv-structures
                            (x86 x86-1)
                            (x86-equiv x86-2)))
           :in-theory (e/d* (rm08
                             xlate-equiv-x86s
                             all-mem-except-paging-structures-equal)
                            (gather-all-paging-structure-qword-addresses-with-xlate-equiv-structures)))))

(defthm mv-nth-2-rm08-and-xlate-equiv-x86s
  (implies (paging-entries-found-p lin-addr (double-rewrite x86))
           (xlate-equiv-x86s
            (mv-nth 2 (rm08 lin-addr r-w-x x86))
            (double-rewrite x86)))
  :hints (("Goal" :in-theory (e/d* (rm08) ()))))

(defthm wm08-values-and-xlate-equiv-structures-disjoint
  (implies (and
            (bind-free
             (find-an-xlate-equiv-x86
              'wm08-values-and-xlate-equiv-x86s-disjoint 'x86-2 x86-1)
             (x86-2))
            (paging-entries-found-p lin-addr (double-rewrite x86-1))
            (xlate-equiv-structures (double-rewrite x86-1) x86-2))
           (equal
            (mv-nth 0 (wm08 lin-addr val x86-1))
            (mv-nth 0 (wm08 lin-addr val x86-2))))
  :hints (("Goal"
           :use ((:instance xlate-equiv-structures-open-for-cpl)
                 (:instance gather-all-paging-structure-qword-addresses-with-xlate-equiv-structures
                            (x86 x86-1)
                            (x86-equiv x86-2)))
           :in-theory (e/d* (wm08
                             xlate-equiv-x86s
                             all-mem-except-paging-structures-equal)
                            (gather-all-paging-structure-qword-addresses-with-xlate-equiv-structures)))))

(defthm mv-nth-1-wm08-and-xlate-equiv-structures-disjoint
  (implies (and (paging-entries-found-p lin-addr (double-rewrite x86))
                (pairwise-disjoint-p-aux
                 ;; The write is not being done to the paging structures.
                 (list
                  (mv-nth
                   1
                   (ia32e-entries-found-la-to-pa
                    lin-addr :w (loghead 2 (xr :seg-visible 1 x86)) x86)))
                 (open-qword-paddr-list-list
                  (gather-all-paging-structure-qword-addresses x86))))
           (xlate-equiv-structures
            (mv-nth 1 (wm08 lin-addr val x86))
            (double-rewrite x86)))
  :hints (("Goal" :in-theory
           (e/d* (wm08)
                 (gather-all-paging-structure-qword-addresses-with-xlate-equiv-structures)))))

;; ======================================================================

(define all-paging-entries-found-p (l-addrs x86)
  :guard (canonical-address-listp l-addrs)
  (if (atom l-addrs)
      (eql l-addrs nil)
    (and (paging-entries-found-p (car l-addrs) x86)
         (all-paging-entries-found-p (cdr l-addrs) x86)))
  ///

  (defthm canonical-address-listp-first-input-to-all-paging-entries-found-p
    (implies (all-paging-entries-found-p l-addrs x86)
             (canonical-address-listp l-addrs))
    :hints (("Goal" :in-theory (e/d* () (signed-byte-p))))
    :rule-classes (:rewrite :forward-chaining))

  (defthm all-paging-entries-found-p-and-xlate-equiv-structures
    (implies (xlate-equiv-structures x86-1 x86-2)
             (equal (all-paging-entries-found-p l-addrs x86-1)
                    (all-paging-entries-found-p l-addrs x86-2)))
    :rule-classes :congruence)

  (defthm all-paging-entries-found-p-and-xlate-equiv-x86s
    (implies (xlate-equiv-x86s x86-1 x86-2)
             (equal (all-paging-entries-found-p l-addrs x86-1)
                    (all-paging-entries-found-p l-addrs x86-2)))
    :rule-classes :congruence)

  (defthm all-paging-entries-found-p-subset-p
    (implies (and (all-paging-entries-found-p l-addrs x86)
                  (subset-p l-addrs-subset l-addrs))
             (all-paging-entries-found-p l-addrs-subset x86))
    :hints (("Goal" :in-theory (e/d* (subset-p) ()))))

  (defthm all-paging-entries-found-p-member-p
    (implies (and (all-paging-entries-found-p l-addrs x86)
                  (member-p lin-addr l-addrs))
             (paging-entries-found-p lin-addr x86)))

  (defthm paging-entries-found-p-after-rm08
    (implies (paging-entries-found-p lin-addr-2 (double-rewrite x86))
             (equal (paging-entries-found-p lin-addr-1 (mv-nth 2 (rm08 lin-addr-2 r-w-x x86)))
                    (paging-entries-found-p lin-addr-1 (double-rewrite x86)))))

  (defthm all-paging-entries-found-p-after-rm08
    (implies (paging-entries-found-p lin-addr-2 (double-rewrite x86))
             (equal (all-paging-entries-found-p l-addrs (mv-nth 2 (rm08 lin-addr-2 r-w-x x86)))
                    (all-paging-entries-found-p l-addrs (double-rewrite x86)))))

  (defthm all-paging-entries-found-p-after-rb-1
    (implies (all-paging-entries-found-p l-addrs-2 (double-rewrite x86))
             (equal (all-paging-entries-found-p l-addrs-1 (mv-nth 2 (rb-1 l-addrs-2 r-w-x x86 acc)))
                    (all-paging-entries-found-p l-addrs-1 (double-rewrite x86))))
    :hints (("Goal" :induct (rb-1 l-addrs-2 r-w-x x86 acc))))

  (defthm all-paging-entries-found-p-after-rb
    (implies (all-paging-entries-found-p l-addrs-2 (double-rewrite x86))
             (equal (all-paging-entries-found-p l-addrs-1 (mv-nth 2 (rb l-addrs-2 r-w-x x86)))
                    (all-paging-entries-found-p l-addrs-1 (double-rewrite x86)))))

  (defthm paging-entries-found-p-after-wm08
    (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
                  (paging-entries-found-p lin-addr-2 (double-rewrite x86))
                  (pairwise-disjoint-p-aux
                   (list (mv-nth 1 (ia32e-entries-found-la-to-pa lin-addr-2 :w cpl x86)))
                   (open-qword-paddr-list-list
                    (gather-all-paging-structure-qword-addresses x86))))
             (equal (paging-entries-found-p lin-addr-1 (mv-nth 1 (wm08 lin-addr-2 val x86)))
                    (paging-entries-found-p lin-addr-1 (double-rewrite x86)))))

  (defthm all-paging-entries-found-p-after-wm08
    (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
                  (paging-entries-found-p lin-addr-2 (double-rewrite x86))
                  (pairwise-disjoint-p-aux
                   (list (mv-nth 1 (ia32e-entries-found-la-to-pa lin-addr-2 :w cpl x86)))
                   (open-qword-paddr-list-list
                    (gather-all-paging-structure-qword-addresses x86))))
             (equal
              (all-paging-entries-found-p l-addrs-1 (mv-nth 1 (wm08 lin-addr-2 val x86)))
              (all-paging-entries-found-p l-addrs-1 (double-rewrite x86)))))

  ;; x86 all-paging-entries-found-p-after-wb and other events about wb
  ;; after mapped-lin-addrs-disjoint-from-paging-structure-addrs-p.
  )

(define no-page-faults-during-translation-p
  (l-addrs
   (r-w-x :type (member :r :w :x))
   (cpl   :type (unsigned-byte 2))
   x86)
  :non-executable t
  :guard (canonical-address-listp l-addrs)
  (if (atom l-addrs)
      (eql l-addrs nil)
    (and (not (mv-nth 0 (ia32e-entries-found-la-to-pa (car l-addrs) r-w-x cpl x86)))
         (no-page-faults-during-translation-p (cdr l-addrs) r-w-x cpl x86)))

  ///

  (defthm no-page-faults-during-translation-p-and-xlate-equiv-structures
    (implies (xlate-equiv-structures x86-1 x86-2)
             (equal (no-page-faults-during-translation-p l-addrs r-w-x cpl x86-1)
                    (no-page-faults-during-translation-p l-addrs r-w-x cpl x86-2)))
    :rule-classes :congruence)

  (defthm no-page-faults-during-translation-p-and-xlate-equiv-x86s
    (implies (xlate-equiv-x86s x86-1 x86-2)
             (equal (no-page-faults-during-translation-p l-addrs r-w-x cpl x86-1)
                    (no-page-faults-during-translation-p l-addrs r-w-x cpl x86-2)))
    :rule-classes :congruence)

  (defthm no-page-faults-during-translation-p-subset-p
    (implies (and (no-page-faults-during-translation-p l-addrs r-w-x cpl x86)
                  (subset-p l-addrs-subset l-addrs))
             (no-page-faults-during-translation-p
              l-addrs-subset r-w-x cpl x86))
    :hints (("Goal" :in-theory (e/d* (subset-p) ()))))

  (defthm no-page-faults-during-translation-p-member-p
    (implies (and (no-page-faults-during-translation-p l-addrs r-w-x cpl (double-rewrite x86))
                  (member-p lin-addr l-addrs))
             (not (mv-nth 0 (ia32e-entries-found-la-to-pa lin-addr r-w-x cpl x86)))))

  (defthm no-page-faults-during-translation-p-after-rm08
    (implies (paging-entries-found-p lin-addr (double-rewrite x86))
             (equal (no-page-faults-during-translation-p l-addrs r-w-x-1 cpl (mv-nth 2 (rm08 lin-addr r-w-x-2 x86)))
                    (no-page-faults-during-translation-p l-addrs r-w-x-1 cpl (double-rewrite x86)))))

  (defthm no-page-faults-during-translation-p-after-rb-1
    (implies (all-paging-entries-found-p l-addrs-2 (double-rewrite x86))
             (equal
              (no-page-faults-during-translation-p l-addrs-1 r-w-x-1 cpl (mv-nth 2 (rb-1 l-addrs-2 r-w-x-2 x86 acc)))
              (no-page-faults-during-translation-p l-addrs-1 r-w-x-1 cpl (double-rewrite x86))))
    :hints (("Goal" :induct (rb-1 l-addrs-2 r-w-x-2 x86 acc))))

  (defthm no-page-faults-during-translation-p-after-rb
    (implies (all-paging-entries-found-p l-addrs-2 (double-rewrite x86))
             (equal (no-page-faults-during-translation-p l-addrs-1 r-w-x-1 cpl (mv-nth 2 (rb l-addrs-2 r-w-x-2 x86)))
                    (no-page-faults-during-translation-p l-addrs-1 r-w-x-1 cpl (double-rewrite x86))                  ))
    :hints (("Goal" :in-theory (e/d* () (rb-1)))))

  (defthm no-page-faults-during-translation-p-after-wm08
    (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
                  (paging-entries-found-p lin-addr-2 (double-rewrite x86))
                  (pairwise-disjoint-p-aux
                   (list (mv-nth 1 (ia32e-entries-found-la-to-pa lin-addr-2 :w cpl x86)))
                   (open-qword-paddr-list-list
                    (gather-all-paging-structure-qword-addresses x86))))
             (equal (no-page-faults-during-translation-p l-addrs-1 r-w-x-1 cpl (mv-nth 1 (wm08 lin-addr-2 val x86)))
                    (no-page-faults-during-translation-p l-addrs-1 r-w-x-1 cpl (double-rewrite x86))))))

(define mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
  (l-addrs
   (r-w-x :type (member :r :w :x))
   (cpl   :type (unsigned-byte 2))
   x86)
  :guard (and (not (xr :programmer-level-mode 0 x86))
              (canonical-address-listp l-addrs))
  :prepwork
  ((defthm open-qword-paddr-list-list-and-true-list-listp
     (true-list-listp (open-qword-paddr-list-list xs))))
  (if (good-paging-structures-x86p x86)
      (if (atom l-addrs)
          (eql l-addrs nil)
        (and (pairwise-disjoint-p-aux
              (list (mv-nth 1 (ia32e-entries-found-la-to-pa (car l-addrs) r-w-x cpl x86)))
              (open-qword-paddr-list-list (gather-all-paging-structure-qword-addresses x86)))
             (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p (cdr l-addrs) r-w-x cpl x86)))
    nil)

  ///

  (defthm mapped-lin-addrs-disjoint-from-paging-structure-addrs-p-and-xlate-equiv-structures
    (implies (xlate-equiv-structures x86-1 x86-2)
             (equal (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p l-addrs r-w-x cpl x86-1)
                    (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p l-addrs r-w-x cpl x86-2)))
    :hints (("Goal"
             :induct (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p l-addrs r-w-x cpl x86-1))
            ("Subgoal *1/3"
             :use ((:instance gather-all-paging-structure-qword-addresses-with-xlate-equiv-structures
                              (x86 x86-1)
                              (x86-equiv x86-2))))
            ("Subgoal *1/2"
             :use ((:instance gather-all-paging-structure-qword-addresses-with-xlate-equiv-structures
                              (x86 x86-1)
                              (x86-equiv x86-2)))))
    :rule-classes :congruence)

  (defthm mapped-lin-addrs-disjoint-from-paging-structure-addrs-p-and-xlate-equiv-x86s
    (implies (xlate-equiv-x86s x86-1 x86-2)
             (equal (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p l-addrs r-w-x cpl x86-1)
                    (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p l-addrs r-w-x cpl x86-2)))
    :hints (("Goal"
             :induct (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p l-addrs r-w-x cpl x86-1))
            ("Subgoal *1/3"
             :use ((:instance gather-all-paging-structure-qword-addresses-with-xlate-equiv-structures
                              (x86 x86-1)
                              (x86-equiv x86-2))))
            ("Subgoal *1/2"
             :use ((:instance gather-all-paging-structure-qword-addresses-with-xlate-equiv-structures
                              (x86 x86-1)
                              (x86-equiv x86-2)))))
    :rule-classes :congruence)

  (defthm mapped-lin-addrs-disjoint-from-paging-structure-addrs-p-subset-p
    (implies (and (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                   l-addrs r-w-x cpl x86)
                  (subset-p l-addrs-subset l-addrs))
             (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p l-addrs-subset r-w-x cpl x86))
    :hints (("Goal" :in-theory (e/d* (subset-p) ()))))

  (defthm mapped-lin-addrs-disjoint-from-paging-structure-addrs-p-member-p
    (implies (and (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                   l-addrs r-w-x cpl (double-rewrite x86))
                  (member-p lin-addr l-addrs))
             (pairwise-disjoint-p-aux
              (list (mv-nth 1 (ia32e-entries-found-la-to-pa lin-addr r-w-x cpl x86)))
              (open-qword-paddr-list-list (gather-all-paging-structure-qword-addresses x86))))
    :hints (("Goal" :in-theory (e/d* (member-p) ()))))

  (defthm mapped-lin-addrs-disjoint-from-paging-structure-addrs-p-after-rm08
    (implies (paging-entries-found-p lin-addr (double-rewrite x86))
             (equal (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                     l-addrs r-w-x-1 cpl (mv-nth 2 (rm08 lin-addr r-w-x-2 x86)))
                    (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                     l-addrs r-w-x-1 cpl (double-rewrite x86)))))

  (defthm mapped-lin-addrs-disjoint-from-paging-structure-addrs-p-after-rb-1
    (implies (all-paging-entries-found-p l-addrs-2 (double-rewrite x86))
             (equal
              (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
               l-addrs-1 r-w-x-1 cpl (mv-nth 2 (rb-1 l-addrs-2 r-w-x-2 x86 acc)))
              (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
               l-addrs-1 r-w-x-1 cpl (double-rewrite x86))))
    :hints (("Goal" :induct (rb-1 l-addrs-2 r-w-x-2 x86 acc))))

  (defthm mapped-lin-addrs-disjoint-from-paging-structure-addrs-p-after-rb
    (implies (all-paging-entries-found-p l-addrs-2 (double-rewrite x86))
             (equal
              (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
               l-addrs-1 r-w-x-1 cpl (mv-nth 2 (rb l-addrs-2 r-w-x-2 x86)))
              (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
               l-addrs-1 r-w-x-1 cpl (double-rewrite x86))))
    :hints (("Goal" :in-theory (e/d* () (rb-1)))))

  (defthm mapped-lin-addrs-disjoint-from-paging-structure-addrs-p-after-wm08
    (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
                  (paging-entries-found-p lin-addr-2 (double-rewrite x86))
                  (pairwise-disjoint-p-aux
                   (list (mv-nth 1 (ia32e-entries-found-la-to-pa lin-addr-2 :w cpl x86)))
                   (open-qword-paddr-list-list
                    (gather-all-paging-structure-qword-addresses x86))))
             (equal (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                     l-addrs-1 r-w-x-1 cpl (mv-nth 1 (wm08 lin-addr-2 val x86)))
                    (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                     l-addrs-1 r-w-x-1 cpl (double-rewrite x86))))))

;; ======================================================================

(defthm mv-nth-2-rb-1-and-xlate-equiv-x86s
  (implies (all-paging-entries-found-p l-addrs (double-rewrite x86))
           (xlate-equiv-x86s
            (mv-nth 2 (rb-1 l-addrs r-w-x x86 acc))
            (double-rewrite x86))))

(defthm mv-nth-2-rb-and-xlate-equiv-x86s
  (implies (all-paging-entries-found-p l-addrs (double-rewrite x86))
           (xlate-equiv-x86s
            (mv-nth 2 (rb l-addrs r-w-x x86))
            (double-rewrite x86)))
  :hints (("Goal" :in-theory (e/d* () (rb-1)))))

(local
 (defthm rm08-returns-no-error-in-system-level-mode
   (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
                 (paging-entries-found-p lin-addr (double-rewrite x86))
                 (not (mv-nth 0 (ia32e-entries-found-la-to-pa lin-addr r-w-x cpl x86))))
            (equal (mv-nth 0 (rm08 lin-addr r-w-x x86)) nil))
   :hints (("Goal" :in-theory (e/d* (rm08) ())))))

(defun-nx rb-1-and-xlate-equiv-structures-ind-hint
  (l-addrs r-w-x x86-1 x86-2 acc)
  (if (endp l-addrs)
      acc
    (rb-1-and-xlate-equiv-structures-ind-hint
     (cdr l-addrs) r-w-x
     (mv-nth 2 (rm08 (car l-addrs) r-w-x x86-1))
     (mv-nth 2 (rm08 (car l-addrs) r-w-x x86-2))
     (append acc (list (mv-nth 1 (rm08 (car l-addrs) r-w-x x86-1)))))))

(local
 (defthmd mv-nth-1-rb-1-and-xlate-equiv-x86s-disjoint-lemma-1
   (implies (and (consp l-addrs)
                 (equal (mv-nth 1
                                (rb-1 (cdr l-addrs)
                                      r-w-x
                                      (mv-nth 2 (rm08 (car l-addrs) r-w-x x86-1))
                                      nil))
                        (mv-nth 1
                                (rb-1 (cdr l-addrs)
                                      r-w-x
                                      (mv-nth 2 (rm08 (car l-addrs) r-w-x x86-2))
                                      nil)))
                 (all-paging-entries-found-p l-addrs x86-1)
                 (xlate-equiv-x86s x86-1 x86-2)
                 (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                  l-addrs r-w-x
                  (loghead 2 (xr :seg-visible 1 x86-1))
                  x86-1)
                 (not (mv-nth 0 (rm08 (car l-addrs) r-w-x x86-1))))
            (equal
             (cons
              (mv-nth 1 (rm08 (car l-addrs) r-w-x x86-1))
              (mv-nth 1
                      (rb-1 (cdr l-addrs)
                            r-w-x
                            (mv-nth 2 (rm08 (car l-addrs) r-w-x x86-1))
                            nil)))
             (mv-nth 1 (rb-1 l-addrs r-w-x x86-2 nil))))
   :hints (("goal"
            :use ((:instance rm08-values-and-xlate-equiv-x86s-disjoint
                             (lin-addr (car l-addrs))))
            :in-theory (e/d* (all-paging-entries-found-p
                              mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                              no-page-faults-during-translation-p)
                             (rm08-values-and-xlate-equiv-x86s-disjoint))))))

(local
 (defthmd mv-nth-1-rb-1-and-xlate-equiv-x86s-disjoint-lemma-2
   (implies (and (true-listp acc)
                 (all-paging-entries-found-p l-addrs x86-1)
                 (xlate-equiv-x86s x86-1 x86-2)
                 (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                  l-addrs r-w-x
                  (loghead 2 (xr :seg-visible 1 x86-1))
                  x86-1)
                 (mv-nth 0 (rm08 (car l-addrs) r-w-x x86-1)))
            (equal (append acc (mv-nth 1 (rb-1 l-addrs r-w-x x86-2 nil)))
                   acc))
   :hints (("Goal"
            :use ((:instance rm08-values-and-xlate-equiv-x86s-disjoint
                             (lin-addr (car l-addrs))))
            :in-theory (e/d* (all-paging-entries-found-p
                              mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                              no-page-faults-during-translation-p)
                             (rm08-values-and-xlate-equiv-x86s-disjoint))))))

(defthm mv-nth-1-rb-1-and-xlate-equiv-x86s-disjoint
  (implies (and
            (bind-free
             (find-an-xlate-equiv-x86
              'mv-nth-1-rb-1-and-xlate-equiv-x86s-disjoint
              'x86-2 x86-1)
             (x86-2))
            (true-listp acc)
            (all-paging-entries-found-p l-addrs (double-rewrite x86-1))
            (xlate-equiv-x86s (double-rewrite x86-1) x86-2)
            (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
             ;; The read is not being done from the paging structures.
             l-addrs r-w-x
             (loghead 2 (xr :seg-visible 1 x86-1))
             (double-rewrite x86-1)))
           (equal
            (mv-nth 1 (rb-1 l-addrs r-w-x x86-1 acc))
            (mv-nth 1 (rb-1 l-addrs r-w-x x86-2 acc))))
  :hints (("Goal"
           :in-theory (e/d* (mv-nth-1-rb-1-and-xlate-equiv-x86s-disjoint-lemma-1
                             mv-nth-1-rb-1-and-xlate-equiv-x86s-disjoint-lemma-2)
                            ())
           :induct (rb-1-and-xlate-equiv-structures-ind-hint l-addrs r-w-x x86-1 x86-2 acc))))

;; (i-am-here)

;; (defthm relating-rm08-and-rb-1-errors
;;   (implies (and
;;             (mv-nth 0 (rm08 (car l-addrs) r-w-x x86))
;;             (canonical-address-listp l-addrs)
;;             (consp l-addrs)
;;             (not (programmer-level-mode x86))
;;             (true-listp acc))
;;            (equal (mv-nth 0 (rb-1 l-addrs r-w-x x86 acc))
;;                   (mv-nth 0 (rm08 (car l-addrs) r-w-x x86)))))

;; (defthm mv-nth-0-rb-1-and-xlate-equiv-x86s-disjoint
;;   ;; I need an rb version of this.
;;   (implies (and
;;             (bind-free
;;              (find-an-xlate-equiv-x86
;;               'mv-nth-0-rb-1-and-xlate-equiv-x86s-disjoint
;;               'x86-2 x86-1)
;;              (x86-2))
;;             (true-listp acc)
;;             (all-paging-entries-found-p l-addrs (double-rewrite x86-1))
;;             (xlate-equiv-x86s (double-rewrite x86-1) x86-2)
;;             (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
;;              ;; The read is not being done from the paging structures.
;;              l-addrs r-w-x
;;              (loghead 2 (xr :seg-visible 1 x86-1))
;;              (double-rewrite x86-1)))
;;            (equal
;;             (mv-nth 0 (rb-1 l-addrs r-w-x x86-1 acc))
;;             (mv-nth 0 (rb-1 l-addrs r-w-x x86-2 acc))))
;;   :hints (("Goal" :in-theory (e/d* () ())
;;            :induct (rb-1-and-xlate-equiv-structures-ind-hint l-addrs r-w-x x86-1 x86-2 acc))))

(defthm mv-nth-1-rb-and-xlate-equiv-x86s-disjoint
  ;; Here, we need xlate-equiv-x86s instead of merely
  ;; xlate-equiv-structures because we need to nilount for the
  ;; equality of all memory locations, apart from those that contain
  ;; the paging structures.
  (implies (and
            (bind-free
             (find-an-xlate-equiv-x86
              'mv-nth-1-rb-and-xlate-equiv-x86s-disjoint
              'x86-2 x86-1)
             (x86-2))
            (all-paging-entries-found-p l-addrs (double-rewrite x86-1))
            (xlate-equiv-x86s (double-rewrite x86-1) x86-2)
            (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
             ;; The read is not being done from the paging structures.
             l-addrs r-w-x
             (loghead 2 (xr :seg-visible 1 x86-1))
             (double-rewrite x86-1)))
           (equal
            (mv-nth 1 (rb l-addrs r-w-x x86-1))
            (mv-nth 1 (rb l-addrs r-w-x x86-2))))
  :hints (("Goal"
           :use ((:instance mv-nth-1-rb-1-and-xlate-equiv-x86s-disjoint
                            (acc nil)))
           :in-theory (e/d* () (mv-nth-1-rb-1-and-xlate-equiv-x86s-disjoint rb-1)))))

(defun-nx wb-and-xlate-equiv-structures-ind-hint
  (l-addrs bytes x86)
  (if (not (equal (len l-addrs) (len bytes)))
      x86
    (if (or (endp l-addrs)
            (endp bytes))
        x86
      (wb-and-xlate-equiv-structures-ind-hint
       (cdr l-addrs)
       (cdr bytes)
       (mv-nth 1 (wm08 (car l-addrs) (car bytes) x86))))))

(defthm wb-values-and-xlate-equiv-structures-disjoint
  (implies (and
            (bind-free
             (find-an-xlate-equiv-x86
              'wb-values-and-xlate-equiv-structures-disjoint
              'x86-2 x86-1)
             (x86-2))
            (all-paging-entries-found-p lin-addr (double-rewrite x86-1))
            (not (programmer-level-mode x86-1))
            (not (programmer-level-mode x86-2)))
           (equal
            (mv-nth 0 (wm08 lin-addr val x86-1))
            (mv-nth 0 (wm08 lin-addr val x86-2))))
  :hints (("Goal" :in-theory (e/d* (wm08) (force (force))))))

(defthm mv-nth-1-wb-and-xlate-equiv-structures-disjoint
  (implies (and (all-paging-entries-found-p l-addrs (double-rewrite x86))
                (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                 ;; The write is not being done to the paging structures.
                 l-addrs :w (loghead 2 (xr :seg-visible 1 x86)) (double-rewrite x86)))
           (xlate-equiv-structures (mv-nth 1 (wb (create-addr-bytes-alist l-addrs bytes) x86))
                                   (double-rewrite x86)))
  :hints (("Goal"
           :induct (wb-and-xlate-equiv-structures-ind-hint l-addrs bytes x86)
           :in-theory
           (e/d* (all-paging-entries-found-p
                  mapped-lin-addrs-disjoint-from-paging-structure-addrs-p)
                 (wm08-values-and-xlate-equiv-structures-disjoint)))))

;; (defthm paging-entries-found-p-after-wb
;;   ;; No need...
;;   (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
;;                 (equal addr-lst (create-addr-bytes-alist l-addrs-2 bytes))
;;                 (all-paging-entries-found-p l-addrs-2 (double-rewrite x86))
;;                 (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
;;                  l-addrs-2 :w cpl (double-rewrite x86)))
;;            (equal (paging-entries-found-p lin-addr-1 (mv-nth 1 (wb addr-lst x86)))
;;                   (paging-entries-found-p lin-addr-1 (double-rewrite x86))))
;;   :hints (("Goal" :in-theory (e/d* (all-paging-entries-found-p
;;                                     mapped-lin-addrs-disjoint-from-paging-structure-addrs-p)
;;                                    ()))))

;; (defthm all-paging-entries-found-p-after-wb
;;   ;; No need...
;;   (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
;;                 (equal addr-lst (create-addr-bytes-alist l-addrs-2 bytes))
;;                 (all-paging-entries-found-p l-addrs-2 (double-rewrite x86))
;;                 (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p l-addrs-2 :w cpl (double-rewrite x86)))
;;            (equal (all-paging-entries-found-p l-addrs-1 (mv-nth 1 (wb addr-lst x86)))
;;                   (all-paging-entries-found-p l-addrs-1 (double-rewrite x86))))
;;   :hints (("Goal" :in-theory (e/d* (all-paging-entries-found-p
;;                                     mapped-lin-addrs-disjoint-from-paging-structure-addrs-p)
;;                                    ()))))

;; ======================================================================

;; A couple of RoW theorems in terms of rm08 and wm08 to get an idea
;; of what kind of lemmas are needed for such proofs in the
;; system-level mode:

(defthmd rm08-wm08-disjoint-in-system-level-mode
  (implies (and (paging-entries-found-p addr-1 x86)
                (paging-entries-found-p addr-2 x86)
                (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
                (not
                 ;; The physical addresses corresponding to addr-1 and
                 ;; addr-2 are different.
                 (equal (mv-nth 1
                                (ia32e-entries-found-la-to-pa addr-1 r-x cpl x86))
                        (mv-nth 1
                                (ia32e-entries-found-la-to-pa addr-2 :w cpl x86))))
                (pairwise-disjoint-p-aux
                 ;; The read isn't being done from the page tables.
                 (list (mv-nth 1
                               (ia32e-entries-found-la-to-pa addr-1 r-x cpl x86)))
                 (open-qword-paddr-list-list
                  (gather-all-paging-structure-qword-addresses x86)))
                (pairwise-disjoint-p-aux
                 ;; The write isn't being done to the page tables ---
                 ;; this means that the translation-governing entries
                 ;; for addr-1 cannot be affected by the write.
                 (list (mv-nth 1
                               (ia32e-entries-found-la-to-pa addr-2 :w cpl x86)))
                 (open-qword-paddr-list-list
                  (gather-all-paging-structure-qword-addresses x86)))
                (unsigned-byte-p 8 val))
           (equal (mv-nth 1 (rm08 addr-1 r-x (mv-nth 1 (wm08 addr-2 val x86))))
                  (mv-nth 1 (rm08 addr-1 r-x x86))))
  :hints (("Goal"
           :use ((:instance gather-all-paging-structure-qword-addresses-xw-fld=mem-disjoint
                            (addrs (gather-all-paging-structure-qword-addresses x86))
                            (index (mv-nth 1 (ia32e-entries-found-la-to-pa addr-2 :w cpl x86)))
                            (val val)
                            (x86 x86)))
           :in-theory (e/d* (ia32e-la-to-pa-and-ia32e-entries-found-la-to-pa
                             rm08
                             wm08)
                            (signed-byte-p
                             unsigned-byte-p
                             gather-all-paging-structure-qword-addresses-xw-fld=mem-disjoint)))))

(defthmd rm08-wm08-equal-in-system-level-mode
  (implies (and (paging-entries-found-p addr-1 x86)
                (paging-entries-found-p addr-2 x86)
                (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
                (equal
                 ;; the physical addresses corresponding to addr-1 and
                 ;; addr-2 are the same.
                 (mv-nth 1 (ia32e-entries-found-la-to-pa addr-1 r-x cpl x86))
                 (mv-nth 1 (ia32e-entries-found-la-to-pa addr-2 :w cpl x86)))
                (pairwise-disjoint-p-aux
                 ;; the write isn't being done to the page tables ---
                 ;; this means that the translation-governing entries
                 ;; for addr-1 cannot be affected by the write.
                 (list (mv-nth 1 (ia32e-entries-found-la-to-pa addr-2 :w cpl x86)))
                 (open-qword-paddr-list-list (gather-all-paging-structure-qword-addresses x86)))
                (not (mv-nth 0 (ia32e-entries-found-la-to-pa addr-1 r-x cpl x86)))
                (not (mv-nth 0 (ia32e-entries-found-la-to-pa addr-2 :w cpl x86)))
                (unsigned-byte-p 8 val))
           (equal (mv-nth 1 (rm08 addr-1 r-x (mv-nth 1 (wm08 addr-2 val x86))))
                  val))
  :hints (("Goal"
           :use ((:instance gather-all-paging-structure-qword-addresses-xw-fld=mem-disjoint
                            (addrs (gather-all-paging-structure-qword-addresses x86))
                            (index (mv-nth 1 (ia32e-entries-found-la-to-pa addr-2 :w cpl x86)))
                            (val val)
                            (x86 x86)))
           :in-theory (e/d* (ia32e-la-to-pa-and-ia32e-entries-found-la-to-pa
                             rm08
                             wm08)
                            (signed-byte-p
                             unsigned-byte-p
                             gather-all-paging-structure-qword-addresses-xw-fld=mem-disjoint)))))

;; ======================================================================

;; Lemmas about rb in the system-level mode:

(local
 (defthm rb-1-returns-no-error-in-system-level-mode-subset
   (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
                 (subset-p l-addrs-subset l-addrs)
                 (all-paging-entries-found-p l-addrs (double-rewrite x86))
                 (no-page-faults-during-translation-p l-addrs r-w-x cpl (double-rewrite x86)))
            (equal (mv-nth 0 (rb-1 l-addrs-subset r-w-x x86 acc)) nil))
   :hints (("Goal"
            :induct (rb-1 l-addrs-subset r-w-x x86 acc)
            :in-theory (e/d* (rm08
                              subset-p
                              all-paging-entries-found-p
                              no-page-faults-during-translation-p)
                             (force (force)))))))

(local
 (defthm rb-1-returns-no-error-in-system-level-mode
   (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
                 (all-paging-entries-found-p l-addrs (double-rewrite x86))
                 (no-page-faults-during-translation-p l-addrs r-w-x cpl (double-rewrite x86)))
            (equal (mv-nth 0 (rb-1 l-addrs r-w-x x86 acc)) nil))
   :hints (("Goal" :in-theory (e/d* (subset-p)
                                    (rb-1-returns-no-error-in-system-level-mode-subset
                                     force (force)))
            :use ((:instance rb-1-returns-no-error-in-system-level-mode-subset
                             (l-addrs-subset l-addrs)))))))

(defthm rb-returns-no-error-in-system-level-mode-subset
  (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
                (subset-p l-addrs-subset l-addrs)
                (all-paging-entries-found-p l-addrs (double-rewrite x86))
                (no-page-faults-during-translation-p l-addrs r-w-x cpl (double-rewrite x86)))
           (equal (mv-nth 0 (rb l-addrs-subset r-w-x x86)) nil))
  :hints (("Goal" :in-theory (e/d* () (rb-1 force (force))))))

(defthm rb-returns-no-error-in-system-level-mode
  (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
                (all-paging-entries-found-p l-addrs (double-rewrite x86))
                (no-page-faults-during-translation-p l-addrs r-w-x cpl (double-rewrite x86)))
           (equal (mv-nth 0 (rb l-addrs r-w-x x86)) nil))
  :hints (("Goal" :in-theory (e/d* () (rb-1 force (force))))))

(local
 (defthm len-of-rb-1-in-system-level-mode
   (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
                 (all-paging-entries-found-p l-addrs (double-rewrite x86))
                 (no-page-faults-during-translation-p l-addrs r-w-x cpl (double-rewrite x86)))
            (equal (len (mv-nth 1 (rb-1 l-addrs r-w-x x86 acc)))
                   (+ (len acc) (len l-addrs))))
   :hints (("Goal"
            :in-theory (e/d* (all-paging-entries-found-p
                              no-page-faults-during-translation-p
                              rm08)
                             (force (force)))
            :induct (rb-1 l-addrs r-w-x x86 acc)))))

(defthm len-of-rb-in-system-level-mode
  (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
                (all-paging-entries-found-p l-addrs (double-rewrite x86))
                (no-page-faults-during-translation-p l-addrs r-w-x cpl (double-rewrite x86)))
           (equal (len (mv-nth 1 (rb l-addrs r-w-x x86))) (len l-addrs)))
  :hints (("Goal" :in-theory (e/d* () (rb-1 force (force))))))

;; Lemmas about wb in system-level mode:

(local
 (defthm wm08-returns-no-error-in-system-level-mode
   (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
                 (paging-entries-found-p lin-addr (double-rewrite x86))
                 (not (mv-nth 0 (ia32e-la-to-pa lin-addr :w cpl x86))))
            (equal (mv-nth 0 (wm08 lin-addr val x86)) nil))
   :hints (("Goal" :in-theory (e/d* (wm08) ())))))

(local
 (defthm wm08-xw-mem-returns-no-error-in-system-level-mode
   (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
                 (paging-entries-found-p lin-addr (double-rewrite x86))
                 (not (mv-nth 0 (ia32e-la-to-pa lin-addr :w cpl x86)))
                 (pairwise-disjoint-p-aux
                  (list index)
                  (open-qword-paddr-list-list
                   (gather-all-paging-structure-qword-addresses x86)))
                 (physical-address-p index)
                 (unsigned-byte-p 8 val))
            (equal (mv-nth 0 (wm08 lin-addr val (xw :mem index val x86)))
                   nil))
   :hints (("Goal" :in-theory (e/d* (wm08) ())))))

(local
 (defthm wm08-wm08-returns-no-error-in-system-level-mode
   (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
                 (paging-entries-found-p lin-addr-1 (double-rewrite x86))
                 (paging-entries-found-p lin-addr-2 (double-rewrite x86))
                 (not (mv-nth 0 (ia32e-entries-found-la-to-pa lin-addr-1 :w cpl x86)))
                 (pairwise-disjoint-p-aux
                  (list (mv-nth 1 (ia32e-entries-found-la-to-pa lin-addr-2 :w cpl x86)))
                  (open-qword-paddr-list-list (gather-all-paging-structure-qword-addresses x86))))
            (equal (mv-nth 0 (wm08 lin-addr-1 val-1 (mv-nth 1 (wm08 lin-addr-2 val-2 x86))))
                   nil))
   :hints (("Goal"
            :in-theory (e/d* (wm08
                              ia32e-la-to-pa-and-ia32e-entries-found-la-to-pa)
                             ())))))

;; (i-am-here)

;; To prove wm08-wm08-commute-in-system-level-mode:

;; (acl2::why ia32e-la-to-pa-and-ia32e-entries-found-la-to-pa)
;; (acl2::why PAGING-ENTRIES-FOUND-P-AND-XW-MEM-DISJOINT-FROM-PAGING-STRUCTURES)

;; (DEFTHM
;;   IA32E-ENTRIES-FOUND-LA-TO-PA-XW-MEM-DISJOINT-FROM-PAGING-STRUCTURES-STATE-new
;;   (IMPLIES
;;    (AND
;;     (PAGING-ENTRIES-FOUND-P LIN-ADDR X86)
;;     (PAIRWISE-DISJOINT-P-AUX
;;      (LIST INDEX)
;;      (OPEN-QWORD-PADDR-LIST-LIST
;;       (GATHER-ALL-PAGING-STRUCTURE-QWORD-ADDRESSES X86)))
;;     (PHYSICAL-ADDRESS-P INDEX)
;;     (UNSIGNED-BYTE-P 8 VAL))
;;    (EQUAL
;;     (MV-NTH 2
;;             (IA32E-ENTRIES-FOUND-LA-TO-PA
;;              LIN-ADDR
;;              R-W-X CPL (XW :MEM INDEX VAL X86)))
;;     (XW
;;      :MEM INDEX VAL
;;      (MV-NTH
;;       2
;;       (IA32E-ENTRIES-FOUND-LA-TO-PA LIN-ADDR R-W-X CPL X86))))))

;; L.H.S.:
;; (XW
;;  :MEM
;;  p-addr-1
;;  val-1
;;  (XW
;;   :MEM
;;   p-addr-2
;;   val-2
;;   (MV-NTH
;;    2
;;    (IA32E-ENTRIES-FOUND-LA-TO-PA
;;     LIN-ADDR-1 r-w-x cpl
;;     (MV-NTH 2 (IA32E-ENTRIES-FOUND-LA-TO-PA
;;             LIN-ADDR-2 r-w-x cpl X86))))))
;; R.H.S:
;; (XW
;;  :MEM
;;  p-addr-2
;;  val-2
;;  (XW
;;   :MEM
;;   p-addr-1
;;   val-1
;;   (MV-NTH
;;    2
;;    (IA32E-ENTRIES-FOUND-LA-TO-PA
;;     LIN-ADDR-2 r-w-x cpl
;;     (MV-NTH
;;      2 (IA32E-ENTRIES-FOUND-LA-TO-PA
;;      LIN-ADDR-1 r-w-x cpl X86))))))

;; Useful rule:
;; (DEFTHM XW-XW-INTRA-FIELD-ARRANGE-WRITES
;;   (IMPLIES (AND (MEMBER FLD *X86-ARRAY-FIELDS-AS-KEYWORDS*)
;;              (NOT (EQUAL I1 I2)))
;;         (EQUAL (XW FLD I2 V2 (XW FLD I1 V1 X86))
;;                (XW FLD I1 V1 (XW FLD I2 V2 X86))))
;;   :RULE-CLASSES ((:REWRITE :LOOP-STOPPER ((I2 I1)))))

;; (local
;;  (defthm wm08-wm08-commute-in-system-level-mode
;;    (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
;;                  (paging-entries-found-p lin-addr-1 x86)
;;                  (paging-entries-found-p lin-addr-2 x86)
;;                  (not
;;                   ;; The physical addresses corresponding to lin-addr-1 and
;;                   ;; lin-addr-2 are different.
;;                   (equal (mv-nth 1 (ia32e-entries-found-la-to-pa lin-addr-1 :w cpl x86))
;;                          (mv-nth 1 (ia32e-entries-found-la-to-pa lin-addr-2 :w cpl x86))))
;;                  (not (mv-nth 0 (ia32e-entries-found-la-to-pa lin-addr-1 :w cpl x86)))
;;                  (not (mv-nth 0 (ia32e-entries-found-la-to-pa lin-addr-2 :w cpl x86)))
;;                  (pairwise-disjoint-p-aux
;;                   (list (mv-nth 1 (ia32e-entries-found-la-to-pa lin-addr-1 :w cpl x86)))
;;                   (open-qword-paddr-list-list (gather-all-paging-structure-qword-addresses x86)))
;;                  (pairwise-disjoint-p-aux
;;                   (list (mv-nth 1 (ia32e-entries-found-la-to-pa lin-addr-2 :w cpl x86)))
;;                   (open-qword-paddr-list-list (gather-all-paging-structure-qword-addresses x86)))
;;                  (not (xr :programmer-level-mode 0 x86)))
;;             (equal (mv-nth 1 (wm08 lin-addr-1 val-1 (mv-nth 1 (wm08 lin-addr-2 val-2 x86))))
;;                    (mv-nth 1 (wm08 lin-addr-2 val-2 (mv-nth 1 (wm08 lin-addr-1 val-1 x86))))))
;;    :hints (("Goal"
;;             :in-theory (e/d* (wm08)
;;                              ())))))

;; (i-am-here)

;; (local (include-book "std/lists/nthcdr" :dir :system))

;; (defun-nx wb-induct-scheme (l-addrs bytes x86)
;;   (if (or (endp l-addrs)
;;           (endp bytes))
;;       x86
;;     (b* ((x86     (mv-nth 1 (wm08 (car l-addrs) (car bytes) x86)))
;;          (l-addrs (cdr l-addrs))
;;          (bytes   (cdr bytes)))
;;       (wb-induct-scheme l-addrs bytes x86))))

;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; ;; To Prove:
;; ;; (equal (mv-nth 0 (wb (create-addr-bytes-alist l-addrs bytes)
;; ;;                      (mv-nth 1 (wm08 lin-addr val x86))))
;; ;;       nil)

;; ;; Assume:

;; ;; (equal (mv-nth 0 (wb (create-addr-bytes-alist (cdr l-addrs) (cdr bytes))
;; ;;                   (mv-nth 1 (wm08
;; ;;                              lin-addr
;; ;;                              val
;; ;;                              (mv-nth 1 (wm08 (car l-addrs) (car bytes) x86))))))
;; ;;        nil)

;; ;; [
;; ;;   x86    : (mv-nth 1 (wm08 (car l-addrs) (car bytes) x86))
;; ;;   l-addrs: (cdr l-addrs)
;; ;;   bytes  : (cdr bytes)
;; ;; ]

;; ;; ==>

;; ;; (equal (mv-nth 0 (wb (create-addr-bytes-alist l-addrs bytes)
;; ;;                   (mv-nth 1 (wm08 lin-addr val x86))))
;; ;;        (mv-nth 0
;; ;;             (wb (create-addr-bytes-alist (cdr l-addrs) (cdr bytes))
;; ;;                 (mv-nth 1 (wm08 (car l-addrs) (car bytes)
;; ;;                                 (mv-nth 1 (wm08 lin-addr val x86)))))))

;; ;; Ugh, I need commutativity of wm08s. Ugh.

;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; (local
;;  (defthm wb-wm08-returns-no-error-in-system-level-mode
;;    (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
;;                  (paging-entries-found-p lin-addr x86)
;;                  (all-paging-entries-found-p l-addrs x86)
;;                  (not (mv-nth 0 (ia32e-entries-found-la-to-pa lin-addr :w cpl x86)))
;;                  (no-page-faults-during-translation-p l-addrs :w cpl x86)
;;                  (pairwise-disjoint-p-aux
;;                   (list (mv-nth 1 (ia32e-entries-found-la-to-pa lin-addr :w cpl x86)))
;;                   (open-qword-paddr-list-list (gather-all-paging-structure-qword-addresses x86)))
;;                  (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p l-addrs :w cpl x86)
;;                  (byte-listp bytes)
;;                  (unsigned-byte-p 8 val))
;;             (equal (mv-nth 0 (wb (create-addr-bytes-alist l-addrs bytes)
;;                                  (mv-nth 1 (wm08 lin-addr val x86))))
;;                    nil))
;;    :hints (("Goal" :induct (wb-induct-scheme l-addrs bytes x86)
;;             :hands-off (wm08)
;;             :in-theory (e/d* ()
;;                              ( ;; ia32e-entries-found-la-to-pa-xw-mem-disjoint-from-paging-structures-state
;;                               ))))))

;; (defthm wb-returns-no-error-in-system-level-mode
;;   (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
;;                 (all-paging-entries-found-p l-addrs x86)
;;                 (no-page-faults-during-translation-p l-addrs :w cpl x86)
;;                 (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p l-addrs :w cpl x86)
;;                 (byte-listp bytes)
;;                 (not (xr :programmer-level-mode 0 x86)))
;;            (equal (mv-nth 0 (wb (create-addr-bytes-alist l-addrs bytes) x86))
;;                   nil)))

;; ======================================================================

;; Relating top-level memory accessors and updaters with rb and wb in
;; system-level mode:

(defthm rm08-to-rb-in-system-level-mode
  (implies (and (not (programmer-level-mode x86))
                (paging-entries-found-p lin-addr (double-rewrite x86)))
           (equal (rm08 lin-addr r-x x86)
                  (b* (((mv flg bytes x86)
                        (rb (create-canonical-address-list 1 lin-addr) r-x x86))
                       (result (combine-bytes bytes)))
                    (mv flg result x86))))
  :hints (("Goal"
           :in-theory (e/d* (ia32e-la-to-pa-and-ia32e-entries-found-la-to-pa
                             rm08
                             rb)
                            (signed-byte-p
                             unsigned-byte-p)))))

(defthm wm08-to-wb-in-system-level-mode
  (implies (and (not (programmer-level-mode x86))
                (paging-entries-found-p lin-addr (double-rewrite x86))
                (unsigned-byte-p 8 byte))
           (equal (wm08 lin-addr byte x86)
                  (wb (create-addr-bytes-alist
                       (create-canonical-address-list 1 lin-addr)
                       (list byte))
                      x86)))
  :hints (("Goal"
           :in-theory (e/d* (ia32e-la-to-pa-and-ia32e-entries-found-la-to-pa
                             wm08
                             wb)
                            (signed-byte-p
                             unsigned-byte-p)))))

;; ----------------------------------------------------------------------

(defthm rm16-to-rb-in-system-level-mode
  (implies
   (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
        (equal l-addrs (create-canonical-address-list 2 lin-addr))
        (equal (len l-addrs) 2)
        (all-paging-entries-found-p l-addrs (double-rewrite x86))
        (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p l-addrs r-w-x cpl (double-rewrite x86))
        (no-page-faults-during-translation-p l-addrs r-w-x cpl (double-rewrite x86)))
   (equal (rm16 lin-addr r-w-x x86)
          (b* (((mv flg bytes x86)
                (rb l-addrs r-w-x x86))
               (result (combine-bytes bytes)))
            (mv flg result x86))))
  :hints (("Goal"
           :in-theory (e/d* (all-paging-entries-found-p
                             mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                             no-page-faults-during-translation-p
                             rm16
                             rm08)
                            (cons-equal
                             signed-byte-p
                             unsigned-byte-p
                             bitops::logior-equal-0
                             rm08-to-rb-in-system-level-mode
                             (:meta acl2::mv-nth-cons-meta)
                             mv-nth-1-rb-1-and-xlate-equiv-x86s-disjoint
                             force (force))))))

(defthm wm16-to-wb-in-system-level-mode
  (implies
   (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
        (equal l-addrs (create-canonical-address-list 2 lin-addr))
        (equal (len l-addrs) 2)
        (all-paging-entries-found-p l-addrs (double-rewrite x86))
        (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p l-addrs :w cpl (double-rewrite x86))
        (no-page-faults-during-translation-p l-addrs :w cpl (double-rewrite x86)))
   (equal (wm16 lin-addr word x86)
          (b* (((mv flg x86)
                (wb (create-addr-bytes-alist l-addrs (byte-ify 2 word)) x86)))
            (mv flg x86))))
  :hints (("Goal"
           :in-theory (e/d* (all-paging-entries-found-p
                             mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                             no-page-faults-during-translation-p
                             wm16
                             wm08
                             byte-ify)
                            (signed-byte-p
                             unsigned-byte-p
                             bitops::logior-equal-0
                             wm08-to-wb-in-system-level-mode
                             (:meta acl2::mv-nth-cons-meta))))))

;; ----------------------------------------------------------------------

(local
 (def-gl-thm rm32-rb-system-level-mode-proof-helper
   :hyp (and (n08p a)
             (n08p b)
             (n08p c)
             (n08p d))
   :concl (equal (logior a (ash b 8) (ash (logior c (ash d 8)) 16))
                 (logior a (ash (logior b (ash (logior c (ash d 8)) 8)) 8)))
   :g-bindings
   (gl::auto-bindings
    (:mix (:nat a 8) (:nat b 8) (:nat c 8) (:nat d 8)))))

(local (in-theory (e/d () (rm32-rb-system-level-mode-proof-helper))))

(defthm rm32-to-rb-in-system-level-mode
  (implies
   (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
        (equal l-addrs (create-canonical-address-list 4 lin-addr))
        (equal (len l-addrs) 4)
        (all-paging-entries-found-p l-addrs (double-rewrite x86))
        (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p l-addrs r-w-x cpl (double-rewrite x86))
        (no-page-faults-during-translation-p l-addrs r-w-x cpl (double-rewrite x86)))
   (equal (rm32 lin-addr r-w-x x86)
          (b* (((mv flg bytes x86)
                (rb l-addrs r-w-x x86))
               (result (combine-bytes bytes)))
            (mv flg result x86))))
  :hints (("Goal"
           :use ((:instance create-canonical-address-list-end-addr-is-canonical
                            (addr lin-addr)
                            (count 4)
                            (end-addr (+ 3 lin-addr))))
           :in-theory (e/d* (all-paging-entries-found-p
                             mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                             no-page-faults-during-translation-p
                             rm32
                             rm08
                             rm32-rb-system-level-mode-proof-helper)
                            (signed-byte-p
                             unsigned-byte-p
                             bitops::logior-equal-0
                             rm08-to-rb-in-system-level-mode
                             (:meta acl2::mv-nth-cons-meta)
                             mv-nth-1-rb-1-and-xlate-equiv-x86s-disjoint
                             force (force))))))

(defthm wm32-to-wb-in-system-level-mode
  (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
                (equal l-addrs (create-canonical-address-list 4 lin-addr))
                (equal (len l-addrs) 4)
                (all-paging-entries-found-p l-addrs (double-rewrite x86))
                (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p l-addrs :w cpl (double-rewrite x86))
                (no-page-faults-during-translation-p l-addrs :w cpl (double-rewrite x86)))
           (equal (wm32 lin-addr dword x86)
                  (b* (((mv flg x86)
                        (wb (create-addr-bytes-alist l-addrs (byte-ify 4 dword))
                            x86)))
                    (mv flg x86))))
  :hints (("Goal"
           :use ((:instance create-canonical-address-list-end-addr-is-canonical
                            (addr lin-addr)
                            (count 4)
                            (end-addr (+ 3 lin-addr))))
           :in-theory (e/d* (all-paging-entries-found-p
                             mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                             no-page-faults-during-translation-p
                             wm32
                             wm08
                             byte-ify)
                            (signed-byte-p
                             unsigned-byte-p
                             bitops::logior-equal-0
                             wm08-to-wb-in-system-level-mode
                             cons-equal
                             (:meta acl2::mv-nth-cons-meta)
                             force (force)
                             ia32e-la-to-pa-lower-12-bits-error
                             loghead-zero-smaller
                             ia32e-la-to-pa-lower-12-bits-value-of-address-when-error
                             good-paging-structures-x86p-implies-x86p)))))

;; ----------------------------------------------------------------------

(local
 (def-gl-thm rm64-to-rb-in-system-level-mode-helper
   :hyp (and (n08p a) (n08p b) (n08p c) (n08p d)
             (n08p e) (n08p f) (n08p g) (n08p h))
   :concl (equal
           (logior a
                   (ash (logior b (ash (logior c (ash d 8)) 8)) 8)
                   (ash (logior e (ash (logior f (ash (logior g (ash h 8)) 8)) 8)) 32))
           (logior
            a
            (ash (logior
                  b
                  (ash (logior
                        c
                        (ash (logior d
                                     (ash
                                      (logior e
                                              (ash
                                               (logior f
                                                       (ash (logior g (ash h 8)) 8)) 8)) 8)) 8)) 8)) 8)))
   :g-bindings
   (gl::auto-bindings
    (:mix (:nat a 8) (:nat b 8) (:nat c 8) (:nat d 8)
          (:nat e 8) (:nat f 8) (:nat g 8) (:nat h 8)))
   :rule-classes :linear))

(local (in-theory (e/d () (rm64-to-rb-in-system-level-mode-helper))))

(defthm rm64-to-rb-in-system-level-mode
  ;; TO-DO: Speed this up.
  ;; Relies on open-create-canonical-address-list.
  (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
                (equal l-addrs (create-canonical-address-list 8 lin-addr))
                (equal (len l-addrs) 8)
                (all-paging-entries-found-p l-addrs (double-rewrite x86))
                (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p l-addrs r-w-x cpl (double-rewrite x86))
                (no-page-faults-during-translation-p l-addrs r-w-x cpl (double-rewrite x86)))
           (equal (rm64 lin-addr r-w-x x86)
                  (b* (((mv flg bytes x86)
                        (rb l-addrs r-w-x x86))
                       (result (combine-bytes bytes)))
                    (mv flg result x86))))
  :hints (("Goal"
           :use ((:instance create-canonical-address-list-end-addr-is-canonical
                            (addr lin-addr)
                            (count 8)
                            (end-addr (+ 7 lin-addr))))
           :in-theory (e/d* (all-paging-entries-found-p
                             mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                             no-page-faults-during-translation-p
                             rm64-to-rb-in-system-level-mode-helper
                             rm64
                             rm08)
                            (signed-byte-p
                             unsigned-byte-p
                             bitops::logior-equal-0
                             rm08-to-rb-in-system-level-mode
                             (:meta acl2::mv-nth-cons-meta)
                             mv-nth-1-rb-1-and-xlate-equiv-x86s-disjoint
                             force (force))))))

(defthm wm64-to-wb-in-system-level-mode
  ;; TO-DO: Speed this up.
  (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
                (equal l-addrs (create-canonical-address-list 8 lin-addr))
                (equal (len l-addrs) 8)
                (all-paging-entries-found-p l-addrs x86)
                (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p l-addrs :w cpl x86)
                (no-page-faults-during-translation-p l-addrs :w cpl x86))
           (equal (wm64 lin-addr qword x86)
                  (b* (((mv flg x86)
                        (wb (create-addr-bytes-alist l-addrs (byte-ify 8 qword))
                            x86)))
                    (mv flg x86))))
  :hints (("Goal"
           :use ((:instance create-canonical-address-list-end-addr-is-canonical
                            (addr lin-addr)
                            (count 8)
                            (end-addr (+ 7 lin-addr))))
           :in-theory (e/d* (all-paging-entries-found-p
                             mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                             no-page-faults-during-translation-p
                             wm64 wm32 wm08
                             byte-ify)
                            (signed-byte-p
                             unsigned-byte-p
                             bitops::logior-equal-0
                             wm08-to-wb-in-system-level-mode
                             mv-nth-1-wm08-and-xlate-equiv-structures-disjoint
                             wm32-to-wb-in-system-level-mode
                             cons-equal
                             (:meta acl2::mv-nth-cons-meta)
                             force (force))))))

;; ======================================================================

(local (in-theory (e/d () (rm08-to-rb-in-system-level-mode
                           wm08-to-wb-in-system-level-mode))))

;; ======================================================================

;; RB returns no error after another RB:

(local
 (defthm rm08-returns-no-error-in-system-level-mode-after-rm08
   (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
                 (paging-entries-found-p lin-addr-1 (double-rewrite x86))
                 (paging-entries-found-p lin-addr-2 (double-rewrite x86))
                 (not (mv-nth 0 (ia32e-la-to-pa lin-addr-1 r-w-x-1 cpl x86))))
            (equal (mv-nth 0 (rm08 lin-addr-1 r-w-x-1 (mv-nth 2 (rm08 lin-addr-2 r-w-x-2 x86))))
                   nil))
   :hints (("Goal" :in-theory (e/d* (rm08) ())))))

(local
 (defthm rm08-returns-no-error-in-system-level-mode-after-rb-1
   (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
                 (paging-entries-found-p lin-addr-1 (double-rewrite x86))
                 (all-paging-entries-found-p l-addrs-2 (double-rewrite x86))
                 (not (mv-nth 0 (ia32e-la-to-pa lin-addr-1 r-w-x-1 cpl x86))))
            (equal (mv-nth 0 (rm08 lin-addr-1 r-w-x-1 (mv-nth 2 (rb-1 l-addrs-2 r-w-x-2 x86 acc-2))))
                   nil))
   :hints (("Goal"
            :induct (rb-1 l-addrs-2 r-w-x-2 x86 acc-2)
            :in-theory (e/d* (rm08) (force (force)))))))

(local
 (defthm rb-1-returns-no-error-in-system-level-mode-after-rb-1
   (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
                 (all-paging-entries-found-p l-addrs-1 (double-rewrite x86))
                 (all-paging-entries-found-p l-addrs-2 (double-rewrite x86))
                 (no-page-faults-during-translation-p l-addrs-1 r-w-x-1 cpl (double-rewrite x86)))
            (equal (mv-nth 0 (rb-1 l-addrs-1 r-w-x-1 (mv-nth 2 (rb-1 l-addrs-2 r-w-x-2 x86 acc-2)) acc-1))
                   nil))
   :hints (("Goal" :induct (rb-1 l-addrs-2 r-w-x-2 x86 acc-2)
            :in-theory (e/d* (rm08) (force (force)))))))

(defthm rb-returns-no-error-in-system-level-mode-after-rb
  (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
                (all-paging-entries-found-p l-addrs-1 (double-rewrite x86))
                (all-paging-entries-found-p l-addrs-2 (double-rewrite x86))
                (no-page-faults-during-translation-p l-addrs-1 r-w-x-1 cpl (double-rewrite x86)))
           (equal (mv-nth 0 (rb l-addrs-1 r-w-x-1 (mv-nth 2 (rb l-addrs-2 r-w-x-2 x86))))
                  nil))
  :hints (("Goal" :in-theory (e/d* () (rb-1 force (force))))))

;; ----------------------------------------------------------------------

;; RB WoW Theorems:

;; (defthm rm08-rm08-WoW-in-system-level-mode
;;   ;; Need similar WoW thms for paging traversal functions...
;;   (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
;;                 ;; A hyp about physical addresses corresponding to
;;                 ;; lin-addr-1 and lin-addr-2 being unequal...
;;                 ...
;;                 (paging-entries-found-p lin-addr-1 x86)
;;                 (paging-entries-found-p lin-addr-2 x86)
;;                 (not (mv-nth 0 (ia32e-la-to-pa lin-addr-1 r-w-x-1 cpl x86))))
;;            (equal (mv-nth 2 (rm08 lin-addr-1 r-w-x-1 (mv-nth 2 (rm08 lin-addr-2 r-w-x-2 x86))))
;;                   (mv-nth 2 (rm08 lin-addr-2 r-w-x-2 (mv-nth 2 (rm08 lin-addr-1 r-w-x-1 x86))))))
;;   :hints (("Goal"
;;            :in-theory (e/d* (rm08
;;                              ia32e-la-to-pa-and-ia32e-entries-found-la-to-pa)
;;                             ()))))


;; (local
;;  (defthm rb-1-rb-1-WoW-in-system-level-mode
;;    (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
;;                  (all-paging-entries-found-p l-addrs-1 x86)
;;                  (all-paging-entries-found-p l-addrs-2 x86)
;;                  (no-page-faults-during-translation-p l-addrs-1 r-w-x-1 cpl x86)
;;                  (no-page-faults-during-translation-p l-addrs-2 r-w-x-2 cpl x86))
;;             (equal (mv-nth 2 (rb-1 l-addrs-2 r-w-x-2 (mv-nth 2 (rb-1 l-addrs-1 r-w-x-1 x86 acc-1)) acc-2))
;;                    (mv-nth 2 (rb-1 l-addrs-1 r-w-x-1 (mv-nth 2 (rb-1 l-addrs-2 r-w-x-2 x86 acc-2)) acc-1))))
;;    :hints (("Goal" :induct (rb-1 l-addrs-2 r-w-x-2 x86 acc-2)
;;             :in-theory (e/d* (ia32e-la-to-pa-and-ia32e-entries-found-la-to-pa
;;                               rm08)
;;                              (force
;;                               (force)
;;                               all-paging-entries-found-p
;;                               no-page-faults-during-translation-p
;;                               mapped-lin-addrs-disjoint-from-paging-structure-addrs-p))))))

;; (defthm rb-rb-WoW-in-system-level-mode
;;   (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
;;                 (all-paging-entries-found-p l-addrs-1 x86)
;;                 (all-paging-entries-found-p l-addrs-2 x86)
;;                 (no-page-faults-during-translation-p l-addrs-1 r-w-x-1 cpl x86)
;;                 (no-page-faults-during-translation-p l-addrs-2 r-w-x-2 cpl x86))
;;            (equal (mv-nth 2 (rb l-addrs-2 r-w-x-2 (mv-nth 2 (rb l-addrs-1 r-w-x-1 x86))))
;;                   (mv-nth 2 (rb l-addrs-1 r-w-x-1 (mv-nth 2 (rb l-addrs-2 r-w-x-2 x86))))))
;;   :hints (("Goal"
;;            :in-theory (e/d* (ia32e-la-to-pa-and-ia32e-entries-found-la-to-pa)
;;                             (rb-1 force (force)
;;                                   all-paging-entries-found-p
;;                                   no-page-faults-during-translation-p
;;                                   mapped-lin-addrs-disjoint-from-paging-structure-addrs-p)))))

;; ----------------------------------------------------------------------

;; Reading via RB after another RB:

(defthm rm08-value-in-system-level-mode-after-rm08
  ;; Need an rb version of this...
  (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
                (paging-entries-found-p lin-addr-1 (double-rewrite x86))
                (paging-entries-found-p lin-addr-2 (double-rewrite x86))
                (pairwise-disjoint-p-aux
                 (list (mv-nth 1 (ia32e-entries-found-la-to-pa lin-addr-1 r-w-x-1 cpl x86)))
                 (open-qword-paddr-list-list (gather-all-paging-structure-qword-addresses x86))))
           (equal (mv-nth 1 (rm08 lin-addr-1 r-w-x-1 (mv-nth 2 (rm08 lin-addr-2 r-w-x-2 x86))))
                  (mv-nth 1 (rm08 lin-addr-1 r-w-x-1 x86))))
  :hints (("Goal" :in-theory (e/d* (rm08)
                                   (mv-nth-2-rm08-and-xlate-equiv-x86s)))))

(local
 (defthm pairwise-disjoint-p-aux-after-rm08-lemma
   (implies (and
             (paging-entries-found-p lin-addr-2 (double-rewrite x86))
             (pairwise-disjoint-p-aux
              (list
               (mv-nth
                1
                (ia32e-entries-found-la-to-pa
                 lin-addr-1 r-w-x-1 (loghead 2 (xr :seg-visible 1 x86)) x86)))
              (open-qword-paddr-list-list
               (gather-all-paging-structure-qword-addresses x86))))
            (pairwise-disjoint-p-aux
             (list (mv-nth 1
                           (ia32e-entries-found-la-to-pa
                            lin-addr-1 r-w-x-1
                            (loghead 2 (xr :seg-visible 1 x86))
                            (mv-nth 2 (rm08 lin-addr-2 r-w-x-2 x86)))))
             (open-qword-paddr-list-list
              (gather-all-paging-structure-qword-addresses
               (mv-nth 2 (rm08 lin-addr-2 r-w-x-2 x86))))))
   :hints (("Goal" :in-theory (e/d* (rm08 ia32e-la-to-pa-and-ia32e-entries-found-la-to-pa)
                                    ())))))

(local
 (defthm ia32e-entries-found-la-to-pa-error-after-rm08
   (implies
    (and (paging-entries-found-p lin-addr-1 (double-rewrite x86))
         (paging-entries-found-p lin-addr-2 (double-rewrite x86))
         (not (mv-nth 0 (ia32e-entries-found-la-to-pa
                         lin-addr-1 r-w-x-1
                         (loghead 2 (xr :seg-visible 1 x86))
                         x86))))
    (not (mv-nth 0 (ia32e-entries-found-la-to-pa
                    lin-addr-1 r-w-x-1
                    (loghead 2 (xr :seg-visible 1 x86))
                    (mv-nth 2 (rm08 lin-addr-2 r-w-x-2 x86))))))
   :hints
   (("Goal"
     :in-theory (e/d* (rm08 ia32e-la-to-pa-and-ia32e-entries-found-la-to-pa)
                      ())))))

;; (local
;;  (defthm rm08-value-in-system-level-mode-after-rb-1
;;    (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
;;                  (paging-entries-found-p lin-addr-1 x86)
;;                  (all-paging-entries-found-p l-addrs-2 x86)
;;                  (pairwise-disjoint-p-aux
;;                   (list (mv-nth 1 (ia32e-entries-found-la-to-pa lin-addr-1 r-w-x-1 cpl x86)))
;;                   (open-qword-paddr-list-list
;;                    (gather-all-paging-structure-qword-addresses x86))))
;;             (equal (mv-nth 1 (rm08 lin-addr-1 r-w-x-1 (mv-nth 2 (rb-1 l-addrs-2 r-w-x-2 x86 acc-2))))
;;                    (mv-nth 1 (rm08 lin-addr-1 r-w-x-1 x86))))
;;    :hints (("Goal"
;;             :induct (rb-1 l-addrs-2 r-w-x-2 x86 acc-2)
;;             :in-theory (e/d* ()
;;                              (force
;;                               (force)
;;                               ;; mv-nth-2-rm08-and-xlate-equiv-x86s
;;                               rm08-values-and-xlate-equiv-x86s-disjoint
;;                               all-paging-entries-found-p
;;                               mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
;;                               no-page-faults-during-translation-p
;;                               ))))))

;; (i-am-here)

;; (thm
;;  (IMPLIES
;;   (AND
;;    (CONSP L-ADDRS-1)
;;    (NOT (MV-NTH 0 (RM08 (CAR L-ADDRS-1) R-W-X-1 X86)))
;;    (EQUAL
;;     (MV-NTH
;;      1
;;      (RB-1 (CDR L-ADDRS-1)
;;            R-W-X-1
;;            (mv-nth 2 (rm08 (car l-addrs-1) r-w-x-1
;;                            (mv-nth 2
;;                                    (rb-1 l-addrs-2 r-w-x-2
;;                                          x86
;;                                          acc-2))))
;;            (APPEND ACC-1
;;                    (LIST (MV-NTH 1
;;                                  (RM08 (CAR L-ADDRS-1) R-W-X-1 X86))))))
;;     (MV-NTH
;;      1
;;      (RB-1 (CDR L-ADDRS-1)
;;            R-W-X-1
;;            (MV-NTH 2 (RM08 (CAR L-ADDRS-1) R-W-X-1 X86))
;;            (APPEND ACC-1
;;                    (LIST (MV-NTH 1
;;                                  (RM08 (CAR L-ADDRS-1) R-W-X-1 X86)))))))
;;    (ALL-PAGING-ENTRIES-FOUND-P L-ADDRS-1 X86)
;;    (ALL-PAGING-ENTRIES-FOUND-P L-ADDRS-2 X86)
;;    (NO-PAGE-FAULTS-DURING-TRANSLATION-P L-ADDRS-1 R-W-X-1
;;                                         (LOGHEAD 2 (XR :SEG-VISIBLE 1 X86))
;;                                         X86)
;;    (NO-PAGE-FAULTS-DURING-TRANSLATION-P L-ADDRS-2 R-W-X-2
;;                                         (LOGHEAD 2 (XR :SEG-VISIBLE 1 X86))
;;                                         X86)
;;    (MAPPED-LIN-ADDRS-DISJOINT-FROM-PAGING-STRUCTURE-ADDRS-P
;;     L-ADDRS-1 R-W-X-1
;;     (LOGHEAD 2 (XR :SEG-VISIBLE 1 X86))
;;     X86))
;;   (EQUAL (MV-NTH 1
;;                  (RB-1 L-ADDRS-1 R-W-X-1
;;                        (MV-NTH 2 (RB-1 L-ADDRS-2 R-W-X-2 X86 ACC-2))
;;                        ACC-1))
;;          (MV-NTH 1
;;                  (RB-1 (CDR L-ADDRS-1)
;;                        R-W-X-1
;;                        (MV-NTH 2 (RM08 (CAR L-ADDRS-1) R-W-X-1 X86))
;;                        (APPEND ACC-1
;;                                (LIST (MV-NTH 1
;;                                              (RM08 (CAR L-ADDRS-1)
;;                                                    R-W-X-1 X86))))))))
;;  :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa-and-ia32e-entries-found-la-to-pa)
;;                                   (mv-nth-2-rm08-and-xlate-equiv-x86s))
;;           :expand (RB-1 L-ADDRS-1 R-W-X-1
;;                         (MV-NTH 2 (RB-1 L-ADDRS-2 R-W-X-2 X86 ACC-2))
;;                         ACC-1))))


;; (local
;;  (defthm rb-1-value-in-system-level-mode-after-rb-1
;;    (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
;;                  (all-paging-entries-found-p l-addrs-1 x86)
;;                  (all-paging-entries-found-p l-addrs-2 x86)
;;                  (no-page-faults-during-translation-p l-addrs-1 r-w-x-1 cpl x86)
;;                  (no-page-faults-during-translation-p l-addrs-2 r-w-x-2 cpl x86)
;;                  (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
;;                   l-addrs-1 r-w-x-1 cpl x86))
;;             (equal (mv-nth 1 (rb-1 l-addrs-1 r-w-x-1 (mv-nth 2 (rb-1 l-addrs-2 r-w-x-2 x86 acc-2)) acc-1))
;;                    (mv-nth 1 (rb-1 l-addrs-1 r-w-x-1 x86 acc-1))))
;;    :hints (("Goal" :induct (rb-1 l-addrs-1 r-w-x-1 x86 acc-1)
;;             :in-theory (e/d* (ia32e-la-to-pa-and-ia32e-entries-found-la-to-pa)
;;                              (force
;;                               (force)
;;                               mv-nth-2-rm08-and-xlate-equiv-x86s
;;                               all-paging-entries-found-p
;;                               no-page-faults-during-translation-p
;;                               mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
;;                               rb-1-accumulator-thm))))))

;; (defthm rb-value-in-system-level-mode-after-rb
;;   (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
;;                 (all-paging-entries-found-p l-addrs-1 x86)
;;                 (all-paging-entries-found-p l-addrs-2 x86)
;;                 (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
;;                  l-addrs-1 r-w-x-1 cpl x86))
;;            (equal (mv-nth 1 (rb l-addrs-1 r-w-x-1 (mv-nth 2 (rb l-addrs-2 r-w-x-2 x86))))
;;                   (mv-nth 1 (rb l-addrs-1 r-w-x-1 x86))))
;;   :hints (("Goal"
;;            :in-theory (e/d* (ia32e-la-to-pa-and-ia32e-entries-found-la-to-pa)
;;                             (rb-1 force (force)
;;                                   all-paging-entries-found-p
;;                                   no-page-faults-during-translation-p
;;                                   mapped-lin-addrs-disjoint-from-paging-structure-addrs-p)))))

;; ;; ----------------------------------------------------------------------

;; ;; Proving rb-rb-split-reads-in-system-level-mode:

;; (defthm rm08-after-ia32e-entries-found-la-to-pa
;;   (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
;;                 (paging-entries-found-p lin-addr-1 x86)
;;                 (paging-entries-found-p lin-addr-2 x86)
;;                 (not (programmer-level-mode x86))
;;                 (pairwise-disjoint-p-aux
;;                  (list
;;                   (mv-nth 1 (ia32e-entries-found-la-to-pa lin-addr-2 r-w-x-2 cpl x86)))
;;                  (open-qword-paddr-list-list
;;                   (gather-all-paging-structure-qword-addresses x86))))
;;            (equal
;;             (mv-nth
;;              1
;;              (rm08
;;               lin-addr-2 r-w-x-2
;;               (mv-nth 2 (ia32e-entries-found-la-to-pa lin-addr-1 r-w-x-1 cpl x86))))
;;             (mv-nth 1 (rm08 lin-addr-2 r-w-x-2 x86))))
;;   :hints
;;   (("Goal" :in-theory (e/d* (ia32e-la-to-pa-and-ia32e-entries-found-la-to-pa
;;                              rm08)
;;                             (force (force))))))

;; (thm
;;  ;; rb-1-after-ia32e-entries-found-la-to-pa needs WoW of
;;  ;; ia32e-entries-found-la-to-pa...  This is a checkpoint in the proof
;;  ;; of rb-1-after-ia32e-entries-found-la-to-pa.
;;  (IMPLIES
;;   (AND
;;    (CONSP L-ADDRS-2)
;;    (NOT (MV-NTH 0 (RM08 (CAR L-ADDRS-2) R-W-X-2 X86)))
;;    (PAGING-ENTRIES-FOUND-P LIN-ADDR-1 X86)
;;    (PAGING-ENTRIES-FOUND-P (CAR L-ADDRS-2)
;;                            X86)
;;    (ALL-PAGING-ENTRIES-FOUND-P (CDR L-ADDRS-2)
;;                                X86)
;;    (NOT (XR :PROGRAMMER-LEVEL-MODE 0 X86))
;;    (PAIRWISE-DISJOINT-P-AUX
;;     (LIST
;;      (MV-NTH 1
;;              (IA32E-ENTRIES-FOUND-LA-TO-PA (CAR L-ADDRS-2)
;;                                            R-W-X-2
;;                                            (LOGHEAD 2 (XR :SEG-VISIBLE 1 X86))
;;                                            X86)))
;;     (OPEN-QWORD-PADDR-LIST-LIST
;;      (GATHER-ALL-PAGING-STRUCTURE-QWORD-ADDRESSES X86)))
;;    (MAPPED-LIN-ADDRS-DISJOINT-FROM-PAGING-STRUCTURE-ADDRS-P
;;     (CDR L-ADDRS-2)
;;     R-W-X-2
;;     (LOGHEAD 2 (XR :SEG-VISIBLE 1 X86))
;;     X86)
;;    (EQUAL
;;     (MV-NTH
;;      1
;;      (RB-1 (CDR L-ADDRS-2)
;;            R-W-X-2
;;            (MV-NTH 2
;;                    (IA32E-ENTRIES-FOUND-LA-TO-PA
;;                     LIN-ADDR-1 R-W-X-1
;;                     (LOGHEAD 2 (XR :SEG-VISIBLE 1 X86))
;;                     (MV-NTH 2 (RM08 (CAR L-ADDRS-2) R-W-X-2 X86))))
;;            (APPEND ACC-2
;;                    (LIST (MV-NTH 1
;;                                  (RM08 (CAR L-ADDRS-2) R-W-X-2 X86))))))
;;     (MV-NTH
;;      1
;;      (RB-1 (CDR L-ADDRS-2)
;;            R-W-X-2
;;            (MV-NTH 2 (RM08 (CAR L-ADDRS-2) R-W-X-2 X86))
;;            (APPEND ACC-2
;;                    (LIST (MV-NTH 1
;;                                  (RM08 (CAR L-ADDRS-2) R-W-X-2 X86))))))))
;;   (EQUAL
;;    (MV-NTH
;;     1
;;     (RB-1
;;      L-ADDRS-2 R-W-X-2
;;      (MV-NTH 2
;;              (IA32E-ENTRIES-FOUND-LA-TO-PA LIN-ADDR-1 R-W-X-1
;;                                            (LOGHEAD 2 (XR :SEG-VISIBLE 1 X86))
;;                                            X86))
;;      ACC-2))
;;    (MV-NTH 1
;;            (RB-1 (CDR L-ADDRS-2)
;;                  R-W-X-2
;;                  (MV-NTH 2 (RM08 (CAR L-ADDRS-2) R-W-X-2 X86))
;;                  (APPEND ACC-2
;;                          (LIST (MV-NTH 1
;;                                        (RM08 (CAR L-ADDRS-2)
;;                                              R-W-X-2 X86))))))))
;;  :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa-and-ia32e-entries-found-la-to-pa
;;                                    rm08)
;;                                   ())
;;           :expand (RB-1
;;                    L-ADDRS-2 R-W-X-2
;;                    (MV-NTH 2
;;                            (IA32E-ENTRIES-FOUND-LA-TO-PA LIN-ADDR-1 R-W-X-1
;;                                                          (LOGHEAD 2 (XR :SEG-VISIBLE 1 X86))
;;                                                          X86))
;;                    ACC-2))))

;; (skip-proofs
;;  (defthm rb-1-after-ia32e-entries-found-la-to-pa
;;    (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
;;                  (paging-entries-found-p lin-addr-1 x86)
;;                  (all-paging-entries-found-p l-addrs-2 x86)
;;                  (not (programmer-level-mode x86))
;;                  (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
;;                   l-addrs-2 r-w-x-2 cpl x86))
;;             (equal (mv-nth 1
;;                            (rb-1
;;                             l-addrs-2 r-w-x-2
;;                             (mv-nth 2 (ia32e-entries-found-la-to-pa lin-addr-1 r-w-x-1 cpl x86))
;;                             acc-2))
;;                    (mv-nth 1 (rb-1 l-addrs-2 r-w-x-2 x86 acc-2))))
;;    :hints
;;    (("Goal"
;;      :induct (rb-1 l-addrs-2 r-w-x-2 x86 acc-2)
;;      :in-theory (e/d* (ia32e-la-to-pa-and-ia32e-entries-found-la-to-pa)
;;                       (force
;;                        rb-1-accumulator-thm
;;                        mv-nth-2-rm08-and-xlate-equiv-x86s
;;                        (force)))))))

;; (defthm rb-rb-split-reads-in-system-level-mode
;;   (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
;;                 (canonical-address-listp l-addrs-1)
;;                 (canonical-address-listp l-addrs-2)
;;                 (equal l-addrs (append l-addrs-1 l-addrs-2))
;;                 (not (programmer-level-mode x86))
;;                 (all-paging-entries-found-p l-addrs x86)
;;                 (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p l-addrs r-w-x cpl x86)
;;                 (no-page-faults-during-translation-p l-addrs r-w-x cpl x86))
;;            (equal (mv-nth 1 (rb l-addrs r-w-x x86))
;;                   (append (mv-nth 1 (rb l-addrs-1 r-w-x x86))
;;                           (mv-nth 1 (rb l-addrs-2 r-w-x x86)))))
;;   :hints (("Goal" :in-theory (e/d* (rm08
;;                                     ia32e-la-to-pa-and-ia32e-entries-found-la-to-pa)
;;                                    ((:meta acl2::mv-nth-cons-meta))))))

;; ======================================================================
