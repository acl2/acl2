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

#||

A list of key theorems in this book:

rm08:

1. Equality of error and value of rm08 from two xlate-equiv-x86s (address disjoint from paging structures)
   [rm08-values-and-xlate-equiv-x86s-disjoint]

2. State returned by rm08 is xlate-equiv-x86s with the original state
   [mv-nth-2-rm08-and-xlate-equiv-x86s]

wm08:

1. Equality of error of wm08 from two xlate-equiv-x86s
   [wm08-values-and-xlate-equiv-structures]

2. State returned by wm08 is xlate-equiv-structures with original state (address disjoint from paging structures)
   [mv-nth-1-wm08-and-xlate-equiv-structures-disjoint]

rb:

1. Equality of error of rb from two xlate-equiv-x86s (addresses disjoint from paging structures)
   [mv-nth-0-rb-and-xlate-equiv-x86s-disjoint]

2. Equality of values of rb from two xlate-equiv-x86s (addresses disjoint from paging structures)
   [mv-nth-1-rb-and-xlate-equiv-x86s-disjoint]

3. State returned by rb is xlate-equiv-x86s with the original state
   [mv-nth-2-rb-and-xlate-equiv-x86s]

4. Conditions under which rb returns no error in the system-level mode
   [rb-returns-no-error-in-system-level-mode]

5. Splitting up the output of one rb into two rbs.
   [rb-rb-split-reads-in-system-level-mode]

wb:

1. Equality of error of wb from two xlate-equiv-x86s
   [wb-values-and-xlate-equiv-structures]

2. State returned by wb is xlate-equiv-structures with original state (addresses disjoint from paging structures)
   [mv-nth-1-wb-and-xlate-equiv-structures-disjoint]

3. Conditions under which wb returns no error in the system-level mode
   [wb-returns-no-error-in-system-level-mode]

||#

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

(defthm wm08-values-and-xlate-equiv-structures
  (implies (and
            (bind-free
             (find-an-xlate-equiv-x86
              'wm08-values-and-xlate-equiv-structures 'x86-2 x86-1)
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
              (all-paging-entries-found-p l-addrs-1 (double-rewrite x86))))))

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
             (equal (no-page-faults-during-translation-p l-addrs-1 r-w-x-1 cpl
                                                         (mv-nth 1 (wm08 lin-addr-2 val x86)))
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

(defthm create-addr-bytes-alist-nil-lemma-1
  (equal (create-addr-bytes-alist l-addrs nil) nil))

(defthm create-addr-bytes-alist-nil-lemma-2
  (equal (create-addr-bytes-alist nil bytes) nil))

(defun-nx wb-ind-hint
  (l-addrs bytes x86)
  (if (not (equal (len l-addrs) (len bytes)))
      x86
    (if (or (endp l-addrs)
            (endp bytes))
        x86
      (wb-ind-hint
       (cdr l-addrs)
       (cdr bytes)
       (mv-nth 1 (wm08 (car l-addrs) (car bytes) x86))))))

(defthm all-paging-entries-found-p-after-wb
  (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
                (all-paging-entries-found-p l-addrs-2 (double-rewrite x86))
                (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                 l-addrs-2 :w cpl (double-rewrite x86))
                (byte-listp bytes))
           (equal
            (all-paging-entries-found-p
             l-addrs-1
             (mv-nth 1 (wb (create-addr-bytes-alist l-addrs-2 bytes) x86)))
            (all-paging-entries-found-p l-addrs-1 (double-rewrite x86))))
  :hints (("Goal"
           :induct (wb-ind-hint l-addrs-2 bytes x86)
           :in-theory (e/d* (all-paging-entries-found-p
                             mapped-lin-addrs-disjoint-from-paging-structure-addrs-p)
                            (wm08-values-and-xlate-equiv-structures)))))

(defthm no-page-faults-during-translation-p-after-wb
  (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
                (all-paging-entries-found-p l-addrs-2 (double-rewrite x86))
                (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                 l-addrs-2 :w cpl (double-rewrite x86))
                (byte-listp bytes))
           (equal (no-page-faults-during-translation-p
                   l-addrs-1 r-w-x-1 cpl
                   (mv-nth 1 (wb (create-addr-bytes-alist l-addrs-2 bytes) x86)))
                  (no-page-faults-during-translation-p
                   l-addrs-1 r-w-x-1 cpl
                   (double-rewrite x86))))
  :hints (("Goal"
           :induct (wb-ind-hint l-addrs-2 bytes x86)
           :in-theory (e/d* (no-page-faults-during-translation-p
                             mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                             all-paging-entries-found-p)
                            (wm08-values-and-xlate-equiv-structures)))))

(defthm mapped-lin-addrs-disjoint-from-paging-structure-addrs-p-after-wb
  (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
                (all-paging-entries-found-p l-addrs-2 (double-rewrite x86))
                (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                 l-addrs-2 :w cpl (double-rewrite x86))
                (byte-listp bytes))
           (equal (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                   l-addrs-1 r-w-x-1 cpl (mv-nth 1 (wb (create-addr-bytes-alist l-addrs-2 bytes) x86)))
                  (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                   l-addrs-1 r-w-x-1 cpl (double-rewrite x86))))
  :hints (("Goal"
           :induct (wb-ind-hint l-addrs-2 bytes x86)
           :in-theory (e/d* (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                             all-paging-entries-found-p)
                            (wm08-values-and-xlate-equiv-structures)))))

;; ======================================================================

(local
 (defthm rm08-returns-no-error-in-system-level-mode
   (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
                 (paging-entries-found-p lin-addr (double-rewrite x86))
                 (not (mv-nth 0 (ia32e-entries-found-la-to-pa lin-addr r-w-x cpl x86))))
            (equal (mv-nth 0 (rm08 lin-addr r-w-x x86)) nil))
   :hints (("Goal" :in-theory (e/d* (rm08) ())))))

(defun-nx rb-1-two-x86s-ind-hint
  (l-addrs r-w-x x86-1 x86-2 acc)
  (if (endp l-addrs)
      acc
    (rb-1-two-x86s-ind-hint
     (cdr l-addrs) r-w-x
     (mv-nth 2 (rm08 (car l-addrs) r-w-x x86-1))
     (mv-nth 2 (rm08 (car l-addrs) r-w-x x86-2))
     (append acc (list (mv-nth 1 (rm08 (car l-addrs) r-w-x x86-1)))))))

(local
 (defthm mv-nth-0-rb-1-and-xlate-equiv-x86s-disjoint
   (implies (and
             (bind-free
              (find-an-xlate-equiv-x86
               'mv-nth-0-rb-1-and-xlate-equiv-x86s-disjoint
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
             (mv-nth 0 (rb-1 l-addrs r-w-x x86-1 acc))
             (mv-nth 0 (rb-1 l-addrs r-w-x x86-2 acc))))
   :hints (("Goal"
            :induct (rb-1-two-x86s-ind-hint l-addrs r-w-x x86-1 x86-2 acc))
           ("Subgoal *1/2"
            :in-theory (e/d* (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p)
                             (rm08-values-and-xlate-equiv-x86s-disjoint))
            :use ((:instance rm08-values-and-xlate-equiv-x86s-disjoint
                             (lin-addr (car l-addrs))))))))

(defthm mv-nth-0-rb-and-xlate-equiv-x86s-disjoint
  (implies (and
            (bind-free
             (find-an-xlate-equiv-x86
              'mv-nth-0-rb-and-xlate-equiv-x86s-disjoint
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
            (mv-nth 0 (rb l-addrs r-w-x x86-1))
            (mv-nth 0 (rb l-addrs r-w-x x86-2))))
  :hints (("Goal"
           :in-theory (e/d* ()
                            (rb-1
                             mv-nth-0-rb-1-and-xlate-equiv-x86s-disjoint))
           :use ((:instance mv-nth-0-rb-1-and-xlate-equiv-x86s-disjoint
                            (acc nil))))))

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

(local
 (defthm mv-nth-1-rb-1-and-xlate-equiv-x86s-disjoint
   (implies (and
             ;; To prevent loops...
             (syntaxp (not (eq x86-1 'x86)))
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
            :induct (rb-1-two-x86s-ind-hint l-addrs r-w-x x86-1 x86-2 acc)))))

(defthm mv-nth-1-rb-and-xlate-equiv-x86s-disjoint
  ;; Here, we need xlate-equiv-x86s instead of merely
  ;; xlate-equiv-structures because we need to nilount for the
  ;; equality of all memory locations, apart from those that contain
  ;; the paging structures.
  (implies (and
            ;; To prevent loops...
            (syntaxp (not (eq x86-1 'x86)))
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

(local
 (defthm mv-nth-2-rb-1-and-xlate-equiv-x86s
   (implies (all-paging-entries-found-p l-addrs (double-rewrite x86))
            (xlate-equiv-x86s
             (mv-nth 2 (rb-1 l-addrs r-w-x x86 acc))
             (double-rewrite x86)))))

(defthm mv-nth-2-rb-and-xlate-equiv-x86s
  (implies (all-paging-entries-found-p l-addrs (double-rewrite x86))
           (xlate-equiv-x86s
            (mv-nth 2 (rb l-addrs r-w-x x86))
            (double-rewrite x86)))
  :hints (("Goal" :in-theory (e/d* () (rb-1)))))

(defthm wb-values-and-xlate-equiv-structures
  (implies (and
            (bind-free
             (find-an-xlate-equiv-x86
              'wb-values-and-xlate-equiv-structures
              'x86-2 x86-1)
             (x86-2))
            (paging-entries-found-p lin-addr (double-rewrite x86-1))
            (xlate-equiv-x86s (double-rewrite x86-1) x86-2))
           (equal
            (mv-nth 0 (wm08 lin-addr val x86-1))
            (mv-nth 0 (wm08 lin-addr val x86-2))))
  :hints (("Goal"
           :use ((:instance xlate-equiv-x86s-open-for-cpl))
           :in-theory (e/d* (wm08) (force (force))))))

(defun-nx wb-ind-hint
  (l-addrs bytes x86)
  (if (not (equal (len l-addrs) (len bytes)))
      x86
    (if (or (endp l-addrs)
            (endp bytes))
        x86
      (wb-ind-hint
       (cdr l-addrs)
       (cdr bytes)
       (mv-nth 1 (wm08 (car l-addrs) (car bytes) x86))))))

(defthm mv-nth-1-wb-and-xlate-equiv-structures-disjoint
  (implies (and (all-paging-entries-found-p l-addrs (double-rewrite x86))
                (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                 ;; The write is not being done to the paging structures.
                 l-addrs :w (loghead 2 (xr :seg-visible 1 x86)) (double-rewrite x86)))
           (xlate-equiv-structures (mv-nth 1 (wb (create-addr-bytes-alist l-addrs bytes) x86))
                                   (double-rewrite x86)))
  :hints (("Goal"
           :induct (wb-ind-hint l-addrs bytes x86)
           :in-theory
           (e/d* (all-paging-entries-found-p
                  mapped-lin-addrs-disjoint-from-paging-structure-addrs-p)
                 (wm08-values-and-xlate-equiv-structures
                  wb-values-and-xlate-equiv-structures)))))

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

(defthm wb-returns-no-error-in-system-level-mode
  (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
                (all-paging-entries-found-p l-addrs (double-rewrite x86))
                (no-page-faults-during-translation-p l-addrs :w cpl (double-rewrite x86))
                (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p l-addrs :w cpl (double-rewrite x86))
                (byte-listp bytes))
           (equal (mv-nth 0 (wb (create-addr-bytes-alist l-addrs bytes) x86)) nil))
  :hints (("Goal"
           :induct (wb-ind-hint l-addrs bytes x86)
           :in-theory (e/d* (no-page-faults-during-translation-p
                             mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                             all-paging-entries-found-p)
                            (rb-1
                             force (force)
                             wm08-values-and-xlate-equiv-structures)))))

;; ======================================================================

;; I should have all the rules that I want about rb and wb by now.
(in-theory (e/d () (rb wb)))

;; RB returns no error after another RB:

(defthm rb-returns-no-error-in-system-level-mode-after-rb
  ;; Follows from rb-returns-no-error-in-system-level-mode. I don't
  ;; really need this theorem.
  (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
                (all-paging-entries-found-p l-addrs-1 (double-rewrite x86))
                (all-paging-entries-found-p l-addrs-2 (double-rewrite x86))
                (no-page-faults-during-translation-p l-addrs-1 r-w-x-1 cpl (double-rewrite x86))
                (not (programmer-level-mode x86)))
           (equal (mv-nth 0 (rb l-addrs-1 r-w-x-1 (mv-nth 2 (rb l-addrs-2 r-w-x-2 x86))))
                  nil))
  :hints (("Goal" :in-theory (e/d* () (force (force))))))

;; Reading via RB after another RB:

(defthm rb-value-in-system-level-mode-after-rb
  ;; Should follow from mv-nth-1-rb-and-xlate-equiv-x86s-disjoint and
  ;; mv-nth-2-rb-and-xlate-equiv-x86s. I don't really need this
  ;; theorem.
  (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
                (all-paging-entries-found-p l-addrs-1 (double-rewrite x86))
                (all-paging-entries-found-p l-addrs-2 (double-rewrite x86))
                (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                 l-addrs-1 r-w-x-1 cpl (double-rewrite x86))
                (not (programmer-level-mode x86)))
           (equal (mv-nth 1 (rb l-addrs-1 r-w-x-1 (mv-nth 2 (rb l-addrs-2 r-w-x-2 x86))))
                  (mv-nth 1 (rb l-addrs-1 r-w-x-1 x86))))
  :hints (("Goal"
           :in-theory (e/d* () (force (force))))))

;; WB returns no error after another WB:

(defthm wb-returns-no-error-in-system-level-mode-after-wb
  ;; Follows from wb-returns-no-error-in-system-level-mode; I don't
  ;; really need this theorem.
  (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
                (all-paging-entries-found-p l-addrs-1 (double-rewrite x86))
                (all-paging-entries-found-p l-addrs-2 (double-rewrite x86))
                (no-page-faults-during-translation-p l-addrs-1 :w cpl (double-rewrite x86))
                (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p l-addrs-1 :w cpl (double-rewrite x86))
                (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p l-addrs-2 :w cpl (double-rewrite x86))
                (byte-listp bytes-1)
                (not (programmer-level-mode x86)))
           (equal (mv-nth 0 (wb (create-addr-bytes-alist l-addrs-1 bytes-1)
                                (mv-nth 1 (wb (create-addr-bytes-alist l-addrs-2 bytes-2)
                                              x86))))
                  nil))
  :hints (("Goal" :in-theory (e/d* () (force (force))))))

;; ----------------------------------------------------------------------

;; Proving rb-rb-split-reads-in-system-level-mode:

(local
 (defthm rb-nil-lemma
   (equal (mv-nth 1 (rb nil r-w-x x86))
          nil)
   :hints (("Goal" :in-theory (e/d* (rb) ())))))

(defthmd rb-rb-split-reads-in-system-level-mode
  (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
                (all-paging-entries-found-p l-addrs (double-rewrite x86))
                (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p l-addrs r-w-x cpl (double-rewrite x86))
                (no-page-faults-during-translation-p l-addrs r-w-x cpl (double-rewrite x86))
                (equal l-addrs (append l-addrs-1 l-addrs-2))
                (canonical-address-listp l-addrs-1)
                (canonical-address-listp l-addrs-2)
                (not (programmer-level-mode x86)))
           (equal (mv-nth 1 (rb l-addrs r-w-x x86))
                  (append (mv-nth 1 (rb l-addrs-1 r-w-x x86))
                          (mv-nth 1 (rb l-addrs-2 r-w-x x86)))))
  :hints (("Goal"
           :in-theory (e/d* (rb
                             all-paging-entries-found-p
                             no-page-faults-during-translation-p)
                            (force (force))))))

;; ======================================================================

;; A couple of RoW theorems in terms of rm08 and wm08 to get an idea
;; of what kind of lemmas are needed for such proofs in the
;; system-level mode:

;; (i-am-here)

;; (local (include-book "std/lists/nthcdr" :dir :system))

;; (define translate-all-l-addrs (l-addrs r-w-x cpl x86)
;;   :guard (and (canonical-address-listp l-addrs)
;;               (member r-w-x '(:r :w :x))
;;               (unsigned-byte-p 2 cpl))
;;   :non-executable t
;;   (if (endp l-addrs)
;;       nil
;;     (b* (((mv flg p-addr x86)
;;           (ia32e-entries-found-la-to-pa (car l-addrs) r-w-x cpl x86))
;;          ((when flg)
;;           nil))
;;       (cons p-addr (translate-all-l-addrs (cdr l-addrs) r-w-x cpl x86)))))

;; (defthm wb-nil-lemma
;;   (equal (mv-nth 1 (wb nil x86))
;;          x86)
;;   :hints (("Goal" :in-theory (e/d* (wb) ()))))

;; (defthmd rb-wb-disjoint-in-system-level-mode
;;   ;; TODO: Formulate an induction scheme.
;;   (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
;;                 (all-paging-entries-found-p l-addrs-1 x86)
;;                 (all-paging-entries-found-p l-addrs-2 x86)
;;                 (not
;;                  ;; The physical addresses corresponding to l-addrs-1
;;                  ;; and l-addrs-2 are different.
;;                  (equal (translate-all-l-addrs l-addrs-1 r-w-x cpl x86)
;;                         (translate-all-l-addrs l-addrs-2    :w cpl x86)))
;;                 (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
;;                  ;; The read isn't being done from the page tables.
;;                  l-addrs-1 r-w-x cpl (double-rewrite x86))
;;                 (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
;;                  ;; The write isn't being done to the page tables.
;;                  l-addrs-2 :w cpl (double-rewrite x86))
;;                 (byte-listp bytes))
;;            (equal (mv-nth 1 (rb l-addrs-1 r-w-x
;;                                 (mv-nth 1 (wb (create-addr-bytes-alist l-addrs-2 bytes) x86))))
;;                   (mv-nth 1 (rb l-addrs-1 r-w-x x86))))
;;   :hints (("Goal" :in-theory (e/d* () (signed-byte-p unsigned-byte-p)))))


;; (defthm rb-wb-equal-in-system-level-mode
;;   (implies (and (all-paging-entries-found-p l-addrs-1 x86)
;;                 (all-paging-entries-found-p l-addrs-2 x86)
;;                 (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))

;;                 (equal
;;                  ;; The physical addresses corresponding to l-addrs-1 and
;;                  ;; l-addrs-2 are the same.
;;                  (mv-nth 1 (ia32e-entries-found-la-to-pa addr-1 r-w-x cpl x86))
;;                  (mv-nth 1 (ia32e-entries-found-la-to-pa addr-2 :w cpl x86)))

;;                 (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
;;                  ;; The read/write isn't being done from/to the page tables.
;;                  l-addrs-2 r-w-x cpl (double-rewrite x86))
;;                 (no-page-faults-during-translation-p l-addrs-1 r-w-x cpl (double-rewrite x86))
;;                 (no-page-faults-during-translation-p l-addrs-2 r-w-x cpl (double-rewrite x86))
;;                 (byte-listp bytes))
;;            (equal (mv-nth 1 (rb l-addrs-1 r-w-x
;;                                 (mv-nth 1 (wb (create-addr-bytes-alist l-addrs-2 bytes) x86))))
;;                   bytes))
;;   :hints (("Goal" :in-theory (e/d* () (signed-byte-p unsigned-byte-p)))))

(defthmd rm08-wm08-disjoint-in-system-level-mode
  (implies (and (paging-entries-found-p addr-1 x86)
                (paging-entries-found-p addr-2 x86)
                (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
                (not
                 ;; The physical addresses corresponding to addr-1 and
                 ;; addr-2 are different.
                 (equal (mv-nth 1
                                (ia32e-entries-found-la-to-pa addr-1 r-w-x cpl x86))
                        (mv-nth 1
                                (ia32e-entries-found-la-to-pa addr-2 :w cpl x86))))
                (pairwise-disjoint-p-aux
                 ;; The read isn't being done from the page tables.
                 (list (mv-nth 1
                               (ia32e-entries-found-la-to-pa addr-1 r-w-x cpl x86)))
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
           (equal (mv-nth 1 (rm08 addr-1 r-w-x (mv-nth 1 (wm08 addr-2 val x86))))
                  (mv-nth 1 (rm08 addr-1 r-w-x x86))))
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
                 (mv-nth 1 (ia32e-entries-found-la-to-pa addr-1 r-w-x cpl x86))
                 (mv-nth 1 (ia32e-entries-found-la-to-pa addr-2 :w cpl x86)))
                (pairwise-disjoint-p-aux
                 ;; the write isn't being done to the page tables ---
                 ;; this means that the translation-governing entries
                 ;; for addr-1 cannot be affected by the write.
                 (list (mv-nth 1 (ia32e-entries-found-la-to-pa addr-2 :w cpl x86)))
                 (open-qword-paddr-list-list (gather-all-paging-structure-qword-addresses x86)))
                (not (mv-nth 0 (ia32e-entries-found-la-to-pa addr-1 r-w-x cpl x86)))
                (not (mv-nth 0 (ia32e-entries-found-la-to-pa addr-2 :w cpl x86)))
                (unsigned-byte-p 8 val))
           (equal (mv-nth 1 (rm08 addr-1 r-w-x (mv-nth 1 (wm08 addr-2 val x86))))
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


;; Relating top-level memory accessors and updaters with rb and wb in
;; system-level mode:

(defthm rm08-to-rb-in-system-level-mode
  (implies (and (not (programmer-level-mode x86))
                (paging-entries-found-p lin-addr (double-rewrite x86)))
           (equal (rm08 lin-addr r-w-x x86)
                  (b* (((mv flg bytes x86)
                        (rb (create-canonical-address-list 1 lin-addr) r-w-x x86))
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
                             rm08
                             rb)
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
                             wb
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
                             rb
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
                             wb
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
                             rm08
                             rb)
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
                             wm64 wm32 wm08 wb
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
