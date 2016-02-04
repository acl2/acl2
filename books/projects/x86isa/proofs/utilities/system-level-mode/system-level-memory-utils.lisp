;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")
(include-book "../general-memory-utils")
(include-book "../x86-row-wow-thms")
(include-book "paging-lib/paging-top")

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "std/lists/nthcdr" :dir :system))

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
   [mv-nth-0-wm08-and-xlate-equiv-structures]

2. State returned by wm08 is xlate-equiv-structures with original state (address disjoint from paging structures)
   [mv-nth-1-wm08-and-xlate-equiv-structures-disjoint]

3. State returned by a wm08 is xlate-equiv-x86s with that returned by
   another wm08, if the same location is modified in the same way in
   both the writes:
   [mv-nth-1-wm08-and-xlate-equiv-x86s-disjoint]

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

6. Rules about rb that will help in fetching and decoding an instruction during reasoning
   [rb-in-terms-of-nth-and-pos-in-system-level-mode]
   [rb-in-terms-of-rb-subset-p-in-system-level-mode]
   [combine-bytes-rb-in-terms-of-rb-subset-p-in-system-level-mode]


wb:

1. Equality of error of wb from two xlate-equiv-structures
   [mv-nth-0-wb-and-xlate-equiv-structures]

2. State returned by wb is xlate-equiv-structures with original state (addresses disjoint from paging structures)
   [mv-nth-1-wb-and-xlate-equiv-structures-disjoint]

3. State returned by a wb is xlate-equiv-x86s with that returned by
   another wb, if the same locations are modified in the same way in
   both the writes:
   [mv-nth-1-wb-and-xlate-equiv-x86s-disjoint]

4. Conditions under which wb returns no error in the system-level mode
   [wb-returns-no-error-in-system-level-mode]

5. Remove shadowed writes from wb
   [wb-remove-duplicate-writes-in-system-level-mode]

program-at:

1. Program-at after a wb returns the same result as though wb didn't
   ever take place, as long as the wb didn't mess up the paging
   structures or the program.
   [program-at-wb-disjoint-in-system-level-mode]

2. Some RoW rules
   [program-at-pop-x86-oracle-in-system-level-mode]
   [program-at-!flgi-in-system-level-mode]
   [program-at-!flgi-undefined-in-system-level-mode]
   [program-at-write-user-rflags-in-system-level-mode]

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

;; ======================================================================

;; Lemmas about rm08 and its relationship with xlate-equiv-x86s:

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
            ;; To prevent loops...
            (syntaxp (not (eq x86-1 x86-2)))
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

;; ----------------------------------------------------------------------

;; Lemmas about wm08 and its relationship with xlate-equiv-structures
;; and xlate-equiv-x86s:

(defthm mv-nth-0-wm08-and-xlate-equiv-structures
  ;; We don't need mv-nth-0-wm08-and-xlate-equiv-x86s because
  ;; xlate-equiv-structures is weaker than xlate-equiv-x86s.
  (implies (and
            (bind-free
             (find-an-xlate-equiv-x86
              'mv-nth-0-wm08-and-xlate-equiv-structures 'x86-2 x86-1)
             (x86-2))
            ;; To prevent loops...
            (syntaxp (not (eq x86-1 x86-2)))
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

(defthm mv-nth-1-wm08-and-xlate-equiv-x86s-disjoint
  (implies (and
            (bind-free
             (find-an-xlate-equiv-x86
              'mv-nth-1-wm08-and-xlate-equiv-x86s-disjoint 'x86-2 x86-1)
             (x86-2))
            ;; To prevent loops...
            (syntaxp (not (eq x86-1 x86-2)))
            (xlate-equiv-x86s (double-rewrite x86-1) x86-2)
            (pairwise-disjoint-p-aux
             ;; The write is not being done to the paging structures.
             (list
              (mv-nth
               1
               (ia32e-entries-found-la-to-pa
                lin-addr :w (loghead 2 (xr :seg-visible 1 x86-1)) x86-1)))
             (open-qword-paddr-list-list
              (gather-all-paging-structure-qword-addresses x86-1)))
            (paging-entries-found-p lin-addr (double-rewrite x86-1)))
           (xlate-equiv-x86s (mv-nth 1 (wm08 lin-addr val x86-1))
                             (mv-nth 1 (wm08 lin-addr val x86-2))))
  :hints (("Goal"
           :use ((:instance xlate-equiv-x86s-open-for-cpl)
                 (:instance xlate-equiv-x86s-and-xw-mem-disjoint
                            (index
                             (mv-nth
                              1
                              (ia32e-entries-found-la-to-pa
                               lin-addr
                               :w (loghead 2 (xr :seg-visible 1 x86-1))
                               x86-1)))
                            (val (loghead 8 val))
                            (x86-1 x86-1)
                            (x86-2 (mv-nth
                                    2
                                    (ia32e-entries-found-la-to-pa
                                     lin-addr
                                     :w (loghead 2 (xr :seg-visible 1 x86-1))
                                     x86-2)))))
           :in-theory (e/d* (wm08)
                            (xlate-equiv-x86s-and-xw-mem-disjoint)))))

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

  ;; (defthm all-paging-entries-found-p-and-xlate-equiv-x86s
  ;;   ;; ACL2 Warning [Equiv] in ( DEFTHM
  ;;   ;; ALL-PAGING-ENTRIES-FOUND-P-AND-XLATE-EQUIV-X86S ...): The
  ;;   ;; previously added :CONGRUENCE lemma,
  ;;   ;; ALL-PAGING-ENTRIES-FOUND-P-AND-XLATE-EQUIV-STRUCTURES,
  ;;   ;; establishes that XLATE-EQUIV-STRUCTURES preserves EQUAL in the
  ;;   ;; second slot of ALL-PAGING-ENTRIES-FOUND-P.  But we know that
  ;;   ;; XLATE-EQUIV-X86S is a refinement of XLATE-EQUIV-STRUCTURES.
  ;;   ;; Thus, ALL-PAGING-ENTRIES-FOUND-P-AND-XLATE-EQUIV-X86S is
  ;;   ;; unnecessary.
  ;;   (implies (xlate-equiv-x86s x86-1 x86-2)
  ;;            (equal (all-paging-entries-found-p l-addrs x86-1)
  ;;                   (all-paging-entries-found-p l-addrs x86-2)))
  ;;   :rule-classes :congruence)

  (defthm all-paging-entries-found-p-subset-p
    (implies (and (all-paging-entries-found-p l-addrs x86)
                  (subset-p l-addrs-subset l-addrs))
             (all-paging-entries-found-p l-addrs-subset x86))
    :hints (("Goal" :in-theory (e/d* (subset-p) ()))))

  (defthm all-paging-entries-found-p-member-p
    (implies (and (all-paging-entries-found-p l-addrs x86)
                  (member-p lin-addr l-addrs))
             (paging-entries-found-p lin-addr x86)))

  (defthm all-paging-entries-found-p-append
    (implies (and (all-paging-entries-found-p l-addrs-1 x86)
                  (all-paging-entries-found-p l-addrs-2 x86))
             (all-paging-entries-found-p (append l-addrs-1 l-addrs-2) x86)))

  ;; (defthm paging-entries-found-p-after-rm08
  ;;   ;; (:REWRITE MV-NTH-2-RM08-AND-XLATE-EQUIV-X86S)
  ;;   ;; (:CONGRUENCE PAGING-ENTRIES-FOUND-P-AND-XLATE-EQUIV-STRUCTURES)
  ;;   (implies (paging-entries-found-p lin-addr-2 (double-rewrite x86))
  ;;            (equal (paging-entries-found-p lin-addr-1 (mv-nth 2 (rm08 lin-addr-2 r-w-x x86)))
  ;;                   (paging-entries-found-p lin-addr-1 (double-rewrite x86)))))

  ;; (defthm all-paging-entries-found-p-after-rm08
  ;;   ;; (:CONGRUENCE ALL-PAGING-ENTRIES-FOUND-P-AND-XLATE-EQUIV-X86S)
  ;;   ;; (:REWRITE MV-NTH-2-RM08-AND-XLATE-EQUIV-X86S)
  ;;   (implies (paging-entries-found-p lin-addr-2 (double-rewrite x86))
  ;;            (equal (all-paging-entries-found-p l-addrs (mv-nth 2 (rm08 lin-addr-2 r-w-x x86)))
  ;;                   (all-paging-entries-found-p l-addrs (double-rewrite x86)))))

  ;; (defthm paging-entries-found-p-after-wm08
  ;;   ;; (:CONGRUENCE PAGING-ENTRIES-FOUND-P-AND-XLATE-EQUIV-STRUCTURES)
  ;;   ;; (:REWRITE MV-NTH-1-WM08-AND-XLATE-EQUIV-STRUCTURES-DISJOINT)
  ;;   (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
  ;;                 (paging-entries-found-p lin-addr-2 (double-rewrite x86))
  ;;                 (pairwise-disjoint-p-aux
  ;;                  (list (mv-nth 1 (ia32e-entries-found-la-to-pa lin-addr-2 :w cpl x86)))
  ;;                  (open-qword-paddr-list-list
  ;;                   (gather-all-paging-structure-qword-addresses x86))))
  ;;            (equal (paging-entries-found-p lin-addr-1 (mv-nth 1 (wm08 lin-addr-2 val x86)))
  ;;                   (paging-entries-found-p lin-addr-1 (double-rewrite x86))))
  ;;   :hints (("Goal" :in-theory (e/d* () (mv-nth-1-wm08-and-xlate-equiv-x86s-disjoint)))))

  ;; (defthm all-paging-entries-found-p-after-wm08
  ;;   ;; (:CONGRUENCE ALL-PAGING-ENTRIES-FOUND-P-AND-XLATE-EQUIV-STRUCTURES)
  ;;   ;; (:REWRITE MV-NTH-1-WM08-AND-XLATE-EQUIV-STRUCTURES-DISJOINT)
  ;;   (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
  ;;                 (paging-entries-found-p lin-addr-2 (double-rewrite x86))
  ;;                 (pairwise-disjoint-p-aux
  ;;                  (list (mv-nth 1 (ia32e-entries-found-la-to-pa lin-addr-2 :w cpl x86)))
  ;;                  (open-qword-paddr-list-list
  ;;                   (gather-all-paging-structure-qword-addresses x86))))
  ;;            (equal
  ;;             (all-paging-entries-found-p l-addrs-1 (mv-nth 1 (wm08 lin-addr-2 val x86)))
  ;;             (all-paging-entries-found-p l-addrs-1 (double-rewrite x86)))))
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

  ;; (defthm no-page-faults-during-translation-p-and-xlate-equiv-x86s
  ;;   (implies (xlate-equiv-x86s x86-1 x86-2)
  ;;            (equal (no-page-faults-during-translation-p l-addrs r-w-x cpl x86-1)
  ;;                   (no-page-faults-during-translation-p l-addrs r-w-x cpl x86-2)))
  ;;   :rule-classes :congruence)

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

  (defthm no-page-faults-during-translation-p-append
    (implies (and (no-page-faults-during-translation-p l-addrs-1 r-w-x cpl x86)
                  (no-page-faults-during-translation-p l-addrs-2 r-w-x cpl x86))
             (no-page-faults-during-translation-p
              (append l-addrs-1 l-addrs-2) r-w-x cpl x86)))

  ;; (defthm no-page-faults-during-translation-p-after-rm08
  ;;   ;; (:CONGRUENCE NO-PAGE-FAULTS-DURING-TRANSLATION-P-AND-XLATE-EQUIV-X86S)
  ;;   ;; (:REWRITE MV-NTH-2-RM08-AND-XLATE-EQUIV-X86S)
  ;;   (implies (paging-entries-found-p lin-addr (double-rewrite x86))
  ;;            (equal (no-page-faults-during-translation-p l-addrs r-w-x-1 cpl
  ;;                                                        (mv-nth 2 (rm08 lin-addr r-w-x-2 x86)))
  ;;                   (no-page-faults-during-translation-p l-addrs r-w-x-1 cpl (double-rewrite x86)))))

  ;; (defthm no-page-faults-during-translation-p-after-wm08
  ;;   ;; (:CONGRUENCE NO-PAGE-FAULTS-DURING-TRANSLATION-P-AND-XLATE-EQUIV-STRUCTURES)
  ;;   ;; (:REWRITE MV-NTH-1-WM08-AND-XLATE-EQUIV-STRUCTURES-DISJOINT)
  ;;   (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
  ;;                 (paging-entries-found-p lin-addr-2 (double-rewrite x86))
  ;;                 (pairwise-disjoint-p-aux
  ;;                  (list (mv-nth 1 (ia32e-entries-found-la-to-pa lin-addr-2 :w cpl x86)))
  ;;                  (open-qword-paddr-list-list
  ;;                   (gather-all-paging-structure-qword-addresses x86))))
  ;;            (equal (no-page-faults-during-translation-p l-addrs-1 r-w-x-1 cpl
  ;;                                                        (mv-nth 1 (wm08 lin-addr-2 val x86)))
  ;;                   (no-page-faults-during-translation-p l-addrs-1 r-w-x-1 cpl (double-rewrite x86)))))
  )

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

  ;; (defthm mapped-lin-addrs-disjoint-from-paging-structure-addrs-p-and-xlate-equiv-x86s
  ;;   (implies (xlate-equiv-x86s x86-1 x86-2)
  ;;            (equal (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p l-addrs r-w-x cpl x86-1)
  ;;                   (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p l-addrs r-w-x cpl x86-2)))
  ;;   :hints (("Goal"
  ;;            :induct (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p l-addrs r-w-x cpl x86-1))
  ;;           ("Subgoal *1/3"
  ;;            :use ((:instance gather-all-paging-structure-qword-addresses-with-xlate-equiv-structures
  ;;                             (x86 x86-1)
  ;;                             (x86-equiv x86-2))))
  ;;           ("Subgoal *1/2"
  ;;            :use ((:instance gather-all-paging-structure-qword-addresses-with-xlate-equiv-structures
  ;;                             (x86 x86-1)
  ;;                             (x86-equiv x86-2)))))
  ;;   :rule-classes :congruence)

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

  (defthm mapped-lin-addrs-disjoint-from-paging-structure-addrs-p-append
    (implies (and (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                   l-addrs-1 r-w-x cpl x86)
                  (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                   l-addrs-2 r-w-x cpl x86))
             (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
              (append l-addrs-1 l-addrs-2) r-w-x cpl x86)))

  ;; (defthm mapped-lin-addrs-disjoint-from-paging-structure-addrs-p-after-rm08
  ;;   ;; (:CONGRUENCE MAPPED-LIN-ADDRS-DISJOINT-FROM-PAGING-STRUCTURE-ADDRS-P-AND-XLATE-EQUIV-X86S)
  ;;   ;; (:REWRITE MV-NTH-2-RM08-AND-XLATE-EQUIV-X86S)
  ;;   (implies (paging-entries-found-p lin-addr (double-rewrite x86))
  ;;            (equal (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
  ;;                    l-addrs r-w-x-1 cpl (mv-nth 2 (rm08 lin-addr r-w-x-2 x86)))
  ;;                   (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
  ;;                    l-addrs r-w-x-1 cpl (double-rewrite x86)))))

  ;; (defthm mapped-lin-addrs-disjoint-from-paging-structure-addrs-p-after-wm08
  ;;   ;; (:CONGRUENCE MAPPED-LIN-ADDRS-DISJOINT-FROM-PAGING-STRUCTURE-ADDRS-P-AND-XLATE-EQUIV-STRUCTURES)
  ;;   ;; (:REWRITE MV-NTH-1-WM08-AND-XLATE-EQUIV-STRUCTURES-DISJOINT)
  ;;   (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
  ;;                 (paging-entries-found-p lin-addr-2 (double-rewrite x86))
  ;;                 (pairwise-disjoint-p-aux
  ;;                  (list (mv-nth 1 (ia32e-entries-found-la-to-pa lin-addr-2 :w cpl x86)))
  ;;                  (open-qword-paddr-list-list
  ;;                   (gather-all-paging-structure-qword-addresses x86))))
  ;;            (equal (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
  ;;                    l-addrs-1 r-w-x-1 cpl (mv-nth 1 (wm08 lin-addr-2 val x86)))
  ;;                   (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
  ;;                    l-addrs-1 r-w-x-1 cpl (double-rewrite x86)))))
  )


;; I don't need the following lemmas anymore. But I'm keeping them
;; around for now to help me prepare an upcoming ACL2 seminar talk.

;; (defthm all-paging-entries-found-p-after-rb-1
;;   ;; (:CONGRUENCE ALL-PAGING-ENTRIES-FOUND-P-AND-XLATE-EQUIV-STRUCTURES)
;;   ;; (:REWRITE MV-NTH-2-RB-1-AND-XLATE-EQUIV-X86S)
;;   (implies (all-paging-entries-found-p l-addrs-2 (double-rewrite x86))
;;            (equal (all-paging-entries-found-p l-addrs-1 (mv-nth 2 (rb-1 l-addrs-2 r-w-x x86 acc)))
;;                   (all-paging-entries-found-p l-addrs-1 (double-rewrite x86)))))

;; (defthm all-paging-entries-found-p-after-rb
;;   ;; (:CONGRUENCE ALL-PAGING-ENTRIES-FOUND-P-AND-XLATE-EQUIV-STRUCTURES)
;;   ;; (:REWRITE MV-NTH-2-RB-AND-XLATE-EQUIV-X86S)
;;   (implies (all-paging-entries-found-p l-addrs-2 (double-rewrite x86))
;;            (equal (all-paging-entries-found-p l-addrs-1 (mv-nth 2 (rb l-addrs-2 r-w-x x86)))
;;                   (all-paging-entries-found-p l-addrs-1 (double-rewrite x86)))))

;; (defthm no-page-faults-during-translation-p-after-rb-1
;;   ;; (:CONGRUENCE NO-PAGE-FAULTS-DURING-TRANSLATION-P-AND-XLATE-EQUIV-STRUCTURES)
;;   ;; (:REWRITE MV-NTH-2-RB-1-AND-XLATE-EQUIV-X86S)
;;   (implies (all-paging-entries-found-p l-addrs-2 (double-rewrite x86))
;;            (equal
;;             (no-page-faults-during-translation-p l-addrs-1 r-w-x-1 cpl
;;                                                  (mv-nth 2 (rb-1 l-addrs-2 r-w-x-2 x86 acc)))
;;             (no-page-faults-during-translation-p l-addrs-1 r-w-x-1 cpl (double-rewrite x86)))))

;; (defthm no-page-faults-during-translation-p-after-rb
;;   (implies (all-paging-entries-found-p l-addrs-2 (double-rewrite x86))
;;            (equal (no-page-faults-during-translation-p l-addrs-1 r-w-x-1 cpl
;;                                                        (mv-nth 2 (rb l-addrs-2 r-w-x-2 x86)))
;;                   (no-page-faults-during-translation-p l-addrs-1 r-w-x-1 cpl (double-rewrite x86)))))

;; (defthm mapped-lin-addrs-disjoint-from-paging-structure-addrs-p-after-rb-1
;;   (implies (all-paging-entries-found-p l-addrs-2 (double-rewrite x86))
;;            (equal
;;             (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
;;              l-addrs-1 r-w-x-1 cpl (mv-nth 2 (rb-1 l-addrs-2 r-w-x-2 x86 acc)))
;;             (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
;;              l-addrs-1 r-w-x-1 cpl (double-rewrite x86)))))

;; (defthm mapped-lin-addrs-disjoint-from-paging-structure-addrs-p-after-rb
;;   (implies (all-paging-entries-found-p l-addrs-2 (double-rewrite x86))
;;            (equal
;;             (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
;;              l-addrs-1 r-w-x-1 cpl (mv-nth 2 (rb l-addrs-2 r-w-x-2 x86)))
;;             (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
;;              l-addrs-1 r-w-x-1 cpl (double-rewrite x86))))
;;   :hints (("Goal" :in-theory (e/d* () (rb)))))

;; (defthm all-paging-entries-found-p-after-wb
;;   (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
;;                 (all-paging-entries-found-p l-addrs-2 (double-rewrite x86))
;;                 (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
;;                  l-addrs-2 :w cpl (double-rewrite x86))
;;                 (byte-listp bytes))
;;            (equal
;;             (all-paging-entries-found-p
;;              l-addrs-1
;;              (mv-nth 1 (wb (create-addr-bytes-alist l-addrs-2 bytes) x86)))
;;             (all-paging-entries-found-p l-addrs-1 (double-rewrite x86))))
;;   :hints (("Goal"
;;            :induct (wb-ind-hint l-addrs-2 bytes x86)
;;            :in-theory (e/d* (all-paging-entries-found-p
;;                              mapped-lin-addrs-disjoint-from-paging-structure-addrs-p)
;;                             (mv-nth-0-wm08-and-xlate-equiv-structures)))))

;; (defthm no-page-faults-during-translation-p-after-wb;;   ;; (:CONGRUENCE ALL-PAGING-ENTRIES-FOUND-P-AND-XLATE-EQUIV-STRUCTURES)
;;   ;; (:REWRITE MV-NTH-1-WB-AND-XLATE-EQUIV-STRUCTURES-DISJOINT)
;;   (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
;;                 (all-paging-entries-found-p l-addrs-2 (double-rewrite x86))
;;                 (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
;;                  l-addrs-2 :w cpl (double-rewrite x86))
;;                 (byte-listp bytes))
;;            (equal (no-page-faults-during-translation-p
;;                    l-addrs-1 r-w-x-1 cpl
;;                    (mv-nth 1 (wb (create-addr-bytes-alist l-addrs-2 bytes) x86)))
;;                   (no-page-faults-during-translation-p
;;                    l-addrs-1 r-w-x-1 cpl
;;                    (double-rewrite x86))))
;;   :hints (("Goal"
;;            :induct (wb-ind-hint l-addrs-2 bytes x86)
;;            :in-theory (e/d* (no-page-faults-during-translation-p
;;                              mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
;;                              all-paging-entries-found-p)
;;                             (mv-nth-0-wm08-and-xlate-equiv-structures)))))

;; (defthm mapped-lin-addrs-disjoint-from-paging-structure-addrs-p-after-wb
;;   ;; (:CONGRUENCE MAPPED-LIN-ADDRS-DISJOINT-FROM-PAGING-STRUCTURE-ADDRS-P-AND-XLATE-EQUIV-STRUCTURES)
;;   ;; (:REWRITE MV-NTH-1-WB-AND-XLATE-EQUIV-STRUCTURES-DISJOINT)
;;   (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
;;                 (all-paging-entries-found-p l-addrs-2 (double-rewrite x86))
;;                 (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
;;                  l-addrs-2 :w cpl (double-rewrite x86))
;;                 (byte-listp bytes))
;;            (equal (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
;;                    l-addrs-1 r-w-x-1 cpl (mv-nth 1 (wb (create-addr-bytes-alist l-addrs-2 bytes) x86)))
;;                   (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
;;                    l-addrs-1 r-w-x-1 cpl (double-rewrite x86))))
;;   :hints (("Goal"
;;            :induct (wb-ind-hint l-addrs-2 bytes x86)
;;            :in-theory (e/d* (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
;;                              all-paging-entries-found-p)
;;                             (mv-nth-0-wm08-and-xlate-equiv-structures)))))

;; ======================================================================

;; Lemmas about rb and its relationship with xlate-equiv-x86s:

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
             (all-paging-entries-found-p l-addrs (double-rewrite x86-1))
             (xlate-equiv-x86s (double-rewrite x86-1) x86-2)
             (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
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
            ;; To prevent loops...
            (syntaxp (not (eq x86-1 x86-2)))
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
   :hints (("Goal"
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
             (bind-free
              (find-an-xlate-equiv-x86
               'mv-nth-1-rb-1-and-xlate-equiv-x86s-disjoint
               'x86-2 x86-1)
              (x86-2))
             ;; To prevent loops...
             (syntaxp (not (eq x86-1 x86-2)))
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
            (bind-free
             (find-an-xlate-equiv-x86
              'mv-nth-1-rb-and-xlate-equiv-x86s-disjoint
              'x86-2 x86-1)
             (x86-2))
            ;; To prevent loops...
            (syntaxp (not (eq x86-1 x86-2)))
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

;; ----------------------------------------------------------------------

;; Lemmas about wb and its relationship with xlate-equiv-structures
;; and xlate-equiv-x86s:

(defun-nx wb-two-x86s-ind-hint
  (addr-bytes x86-1 x86-2)
  (if (endp addr-bytes)
      (mv x86-1 x86-2)
    (wb-two-x86s-ind-hint
     (cdr addr-bytes)
     (mv-nth 1 (wm08 (caar addr-bytes) (cdar addr-bytes) x86-1))
     (mv-nth 1 (wm08 (caar addr-bytes) (cdar addr-bytes) x86-2)))))

(defthm mv-nth-0-wb-and-xlate-equiv-structures
  (implies (and (bind-free
                 (find-an-xlate-equiv-x86
                  'mv-nth-0-wb-and-xlate-equiv-structures 'x86-2 x86-1)
                 (x86-2))
                ;; To prevent loops...
                (syntaxp (not (eq x86-1 x86-2)))
                (xlate-equiv-structures (double-rewrite x86-1) x86-2)
                (all-paging-entries-found-p (strip-cars addr-bytes) (double-rewrite x86-1))
                (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                 (strip-cars addr-bytes) :w (loghead 2 (xr :seg-visible 1 x86-1))
                 (double-rewrite x86-1)))
           (equal
            (mv-nth 0 (wb addr-bytes x86-1))
            (mv-nth 0 (wb addr-bytes x86-2))))
  :hints (("Goal"
           :induct (wb-two-x86s-ind-hint addr-bytes x86-1 x86-2)
           :in-theory (e/d* (all-paging-entries-found-p
                             mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                             wb)
                            (mv-nth-0-wm08-and-xlate-equiv-structures)))
          ("Subgoal *1/2"
           :use ((:instance mv-nth-1-wm08-and-xlate-equiv-structures-disjoint
                            (lin-addr (caar addr-bytes))
                            (val (cdar addr-bytes))
                            (x86 x86-2))
                 (:instance mv-nth-1-wm08-and-xlate-equiv-structures-disjoint
                            (lin-addr (caar addr-bytes))
                            (val (cdar addr-bytes))
                            (x86 x86-1))
                 (:instance mv-nth-0-wm08-and-xlate-equiv-structures
                            (lin-addr (caar addr-bytes))
                            (val (cdar addr-bytes))
                            (x86-1 x86-1)
                            (x86-2 x86-2))
                 (:instance xlate-equiv-structures-open-for-cpl)
                 (:instance gather-all-paging-structure-qword-addresses-with-xlate-equiv-structures
                            (x86 x86-1)
                            (x86-equiv x86-2)))
           :in-theory (e/d* (all-paging-entries-found-p
                             mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                             wb)
                            (mv-nth-0-wm08-and-xlate-equiv-structures
                             mv-nth-1-wm08-and-xlate-equiv-structures-disjoint)))))

(defun-nx wb-ind-hint
  (addr-bytes x86)
  (if (endp addr-bytes)
      x86
    (wb-ind-hint
     (cdr addr-bytes)
     (mv-nth 1 (wm08 (caar addr-bytes) (cdar addr-bytes) x86)))))

(defthm mv-nth-1-wb-and-xlate-equiv-structures-disjoint
  (implies (and (all-paging-entries-found-p (strip-cars addr-bytes) (double-rewrite x86))
                (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                 ;; The write is not being done to the paging structures.
                 (strip-cars addr-bytes) :w (loghead 2 (xr :seg-visible 1 x86)) (double-rewrite x86)))
           (xlate-equiv-structures (mv-nth 1 (wb addr-bytes x86)) (double-rewrite x86)))
  :hints (("Goal"
           :induct (wb-ind-hint addr-bytes x86)
           :in-theory
           (e/d* (all-paging-entries-found-p
                  mapped-lin-addrs-disjoint-from-paging-structure-addrs-p)
                 (mv-nth-0-wm08-and-xlate-equiv-structures)))))

(defthm mv-nth-1-wb-and-xlate-equiv-x86s-disjoint
  (implies (and
            (bind-free
             (find-an-xlate-equiv-x86 'mv-nth-1-wb-and-xlate-equiv-x86s-disjoint 'x86-2 x86-1)
             (x86-2))
            ;; To prevent loops...
            (syntaxp (not (eq x86-1 x86-2)))
            (xlate-equiv-x86s (double-rewrite x86-1) x86-2)
            (all-paging-entries-found-p (strip-cars addr-bytes) (double-rewrite x86-1))
            (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
             ;; The write is not being done to the paging structures.
             (strip-cars addr-bytes)
             :w (loghead 2 (xr :seg-visible 1 x86-1)) (double-rewrite x86-1)))
           (xlate-equiv-x86s
            (mv-nth 1 (wb addr-bytes x86-1))
            (mv-nth 1 (wb addr-bytes x86-2))))
  :hints (("Goal"
           :induct (wb-two-x86s-ind-hint addr-bytes x86-1 x86-2)
           :in-theory (e/d* (all-paging-entries-found-p
                             mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                             wb)
                            (mv-nth-0-wm08-and-xlate-equiv-structures)))
          ("Subgoal *1/2"
           :use ((:instance mv-nth-1-wm08-and-xlate-equiv-x86s-disjoint
                            (lin-addr (caar addr-bytes))
                            (val (cdar addr-bytes))
                            (x86-1 x86-1)
                            (x86-2 x86-2))
                 (:instance mv-nth-0-wm08-and-xlate-equiv-structures
                            (lin-addr (caar addr-bytes))
                            (val (cdar addr-bytes))
                            (x86-1 x86-1)
                            (x86-2 x86-2)))
           :in-theory (e/d* (all-paging-entries-found-p
                             mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                             wb)
                            (mv-nth-0-wm08-and-xlate-equiv-structures)))))

;; ======================================================================

;; Lemmas about rb returning no error in the system-level mode:

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

;; ----------------------------------------------------------------------

;; Lemmas about wb returning no error in system-level mode:

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
                (all-paging-entries-found-p (strip-cars addr-bytes) (double-rewrite x86))
                (no-page-faults-during-translation-p (strip-cars addr-bytes) :w cpl (double-rewrite x86))
                (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p (strip-cars addr-bytes) :w cpl (double-rewrite x86))
                (addr-byte-alistp addr-bytes))
           (equal (mv-nth 0 (wb addr-bytes x86)) nil))
  :hints (("Goal"
           :induct (wb-ind-hint addr-bytes x86)
           :in-theory (e/d* (no-page-faults-during-translation-p
                             mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                             all-paging-entries-found-p)
                            (rb-1
                             force (force)
                             mv-nth-0-wm08-and-xlate-equiv-structures)))))

;; I should have all the rules that I want about rb and wb by now.
(in-theory (e/d () (rb wb)))

;; ----------------------------------------------------------------------

;; Testing the claim that I have sufficient lemmas about rb and wb:

;; RB returns no error after another RB:

(local
 (defthm rb-returns-no-error-in-system-level-mode-after-rb
   ;; (:CONGRUENCE ALL-PAGING-ENTRIES-FOUND-P-AND-XLATE-EQUIV-STRUCTURES)
   ;; (:CONGRUENCE NO-PAGE-FAULTS-DURING-TRANSLATION-P-AND-XLATE-EQUIV-STRUCTURES)
   ;; (:REWRITE MV-NTH-2-RB-AND-XLATE-EQUIV-X86S)
   (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
                 (all-paging-entries-found-p l-addrs-1 (double-rewrite x86))
                 (all-paging-entries-found-p l-addrs-2 (double-rewrite x86))
                 (no-page-faults-during-translation-p l-addrs-1 r-w-x-1 cpl (double-rewrite x86))
                 (not (programmer-level-mode x86)))
            (equal (mv-nth 0 (rb l-addrs-1 r-w-x-1 (mv-nth 2 (rb l-addrs-2 r-w-x-2 x86))))
                   nil))
   :hints (("Goal" :in-theory (e/d* () (force (force)))))))

;; Reading via RB after another RB:

(local
 (defthm rb-value-in-system-level-mode-after-rb
   ;; (:CONGRUENCE ALL-PAGING-ENTRIES-FOUND-P-AND-XLATE-EQUIV-STRUCTURES)
   ;; (:CONGRUENCE MAPPED-LIN-ADDRS-DISJOINT-FROM-PAGING-STRUCTURE-ADDRS-P-AND-XLATE-EQUIV-STRUCTURES)
   ;; (:REWRITE MV-NTH-1-RB-AND-XLATE-EQUIV-X86S-DISJOINT)
   ;; (:REWRITE MV-NTH-2-RB-AND-XLATE-EQUIV-X86S)
   (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
                 (all-paging-entries-found-p l-addrs-1 (double-rewrite x86))
                 (all-paging-entries-found-p l-addrs-2 (double-rewrite x86))
                 (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                  l-addrs-1 r-w-x-1 cpl (double-rewrite x86))
                 (not (programmer-level-mode x86)))
            (equal (mv-nth 1 (rb l-addrs-1 r-w-x-1 (mv-nth 2 (rb l-addrs-2 r-w-x-2 x86))))
                   (mv-nth 1 (rb l-addrs-1 r-w-x-1 x86))))
   :hints (("Goal"
            :in-theory (e/d* () (force (force)))))))

;; WB returns no error after another WB:

(local
 (defthm wb-returns-no-error-in-system-level-mode-after-wb
   ;; (:CONGRUENCE ALL-PAGING-ENTRIES-FOUND-P-AND-XLATE-EQUIV-STRUCTURES)
   ;; (:CONGRUENCE MAPPED-LIN-ADDRS-DISJOINT-FROM-PAGING-STRUCTURE-ADDRS-P-AND-XLATE-EQUIV-STRUCTURES)
   ;; (:CONGRUENCE NO-PAGE-FAULTS-DURING-TRANSLATION-P-AND-XLATE-EQUIV-STRUCTURES)
   ;; (:REWRITE MV-NTH-1-WB-AND-XLATE-EQUIV-STRUCTURES-DISJOINT)
   (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
                 (all-paging-entries-found-p l-addrs-1 (double-rewrite x86))
                 (all-paging-entries-found-p l-addrs-2 (double-rewrite x86))
                 (no-page-faults-during-translation-p
                  l-addrs-1 :w cpl (double-rewrite x86))
                 (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                  l-addrs-1 :w cpl (double-rewrite x86))
                 (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                  l-addrs-2 :w cpl (double-rewrite x86))
                 (byte-listp bytes-1)
                 (equal (len l-addrs-1) (len bytes-1))
                 (equal (len l-addrs-2) (len bytes-2))
                 (not (programmer-level-mode x86)))
            (equal (mv-nth 0 (wb (create-addr-bytes-alist l-addrs-1 bytes-1)
                                 (mv-nth 1 (wb (create-addr-bytes-alist l-addrs-2 bytes-2)
                                               x86))))
                   nil))
   :hints (("Goal"
            :do-not-induct t
            :in-theory (e/d* () (force (force)))))))

;; ======================================================================

;; Proving rb-rb-split-reads-in-system-level-mode:

(defthmd rb-rb-split-reads-in-system-level-mode-aux
  ;; The hyps are in terms of l-addrs instead of l-addrs-1 and
  ;; l-addrs-2 here because likely, that's how we'd want to use this
  ;; rule --- in terms of the larger set of addresses, unlike
  ;; rb-rb-split-reads-in-system-level-mode-state.
  (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
                (all-paging-entries-found-p l-addrs (double-rewrite x86))
                (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                 l-addrs r-w-x cpl (double-rewrite x86))
                (no-page-faults-during-translation-p
                 l-addrs r-w-x cpl (double-rewrite x86))
                (equal l-addrs (append l-addrs-1 l-addrs-2))
                (canonical-address-listp l-addrs-1)
                (canonical-address-listp l-addrs-2))
           (equal (mv-nth 1 (rb l-addrs r-w-x x86))
                  (append (mv-nth 1 (rb l-addrs-1 r-w-x x86))
                          (mv-nth 1 (rb l-addrs-2 r-w-x x86)))))
  :hints (("Goal"
           :in-theory (e/d* (rb
                             all-paging-entries-found-p
                             no-page-faults-during-translation-p)
                            (force (force))))))

(defthm rb-rb-split-reads-in-system-level-mode
  (implies
   (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
        (all-paging-entries-found-p l-addrs-1 (double-rewrite x86))
        (all-paging-entries-found-p l-addrs-2 (double-rewrite x86))
        (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
         l-addrs-1 r-w-x cpl (double-rewrite x86))
        (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
         l-addrs-2 r-w-x cpl (double-rewrite x86))
        (no-page-faults-during-translation-p
         l-addrs-1 r-w-x cpl (double-rewrite x86))
        (no-page-faults-during-translation-p
         l-addrs-2 r-w-x cpl (double-rewrite x86))
        (canonical-address-listp l-addrs-1)
        (canonical-address-listp l-addrs-2))
   (equal (append (mv-nth 1 (rb l-addrs-1 r-w-x x86))
                  (mv-nth 1 (rb l-addrs-2 r-w-x x86)))
          (mv-nth 1 (rb (append l-addrs-1 l-addrs-2) r-w-x x86))))
  :hints
  (("goal"
    :use ((:instance rb-rb-split-reads-in-system-level-mode-aux
                     (l-addrs (append l-addrs-1 l-addrs-2))))
    :in-theory (e/d* () (force (force))))))

(local
 (defthmd rb-rb-split-reads-in-system-level-mode-state-helper
   (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
                 (all-paging-entries-found-p l-addrs (double-rewrite x86))
                 (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                  l-addrs r-w-x cpl (double-rewrite x86))
                 (no-page-faults-during-translation-p
                  l-addrs r-w-x cpl (double-rewrite x86))
                 (equal l-addrs (append l-addrs-1 l-addrs-2))
                 (canonical-address-listp l-addrs-1))
            (equal (mv-nth 2 (rb l-addrs-2 r-w-x (mv-nth 2 (rb l-addrs-1 r-w-x x86))))
                   (mv-nth 2 (rb l-addrs r-w-x x86))))
   :hints (("Goal"
            :in-theory (e/d* (rb
                              all-paging-entries-found-p
                              no-page-faults-during-translation-p)
                             (force (force))))
           ("Subgoal *1/7"
            :use ((:instance mv-nth-2-rb-1-and-accumulator
                             (l-addrs (append (cdr l-addrs-1) l-addrs-2))
                             (r-w-x r-w-x)
                             (x86 (mv-nth 2 (rm08 (car l-addrs-1) r-w-x x86)))
                             (acc-1 (list (mv-nth 1 (rm08 (car l-addrs-1) r-w-x x86))))
                             (acc-2 nil))
                  (:instance mv-nth-2-rb-1-and-accumulator
                             (l-addrs (cdr l-addrs-1))
                             (r-w-x r-w-x)
                             (x86 (mv-nth 2 (rm08 (car l-addrs-1) r-w-x x86)))
                             (acc-1 (list (mv-nth 1 (rm08 (car l-addrs-1) r-w-x x86))))
                             (acc-2 nil)))
            :in-theory (e/d* (rb
                              all-paging-entries-found-p
                              no-page-faults-during-translation-p)
                             (force (force)))))))

(defthm rb-rb-split-reads-in-system-level-mode-state
  ;; The hyps are in terms of l-addrs-1 and l-addrs-2 because we want
  ;; to "combine" the states after these two reads into one
  ;; s-expression...
  (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
                (all-paging-entries-found-p l-addrs-1 (double-rewrite x86))
                (all-paging-entries-found-p l-addrs-2 (double-rewrite x86))
                (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                 l-addrs-1 r-w-x cpl (double-rewrite x86))
                (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                 l-addrs-2 r-w-x cpl (double-rewrite x86))
                (no-page-faults-during-translation-p
                 l-addrs-1 r-w-x cpl (double-rewrite x86))
                (no-page-faults-during-translation-p
                 l-addrs-2 r-w-x cpl (double-rewrite x86)))
           (equal (mv-nth 2 (rb l-addrs-2 r-w-x (mv-nth 2 (rb l-addrs-1 r-w-x x86))))
                  (mv-nth 2 (rb (append l-addrs-1 l-addrs-2) r-w-x x86))))
  :hints (("Goal"
           :use ((:instance rb-rb-split-reads-in-system-level-mode-state-helper
                            (l-addrs (append l-addrs-1 l-addrs-2))))
           :in-theory (e/d* () (force (force))))))

(defun-nx wb-splits-ind-hint
  (addr-bytes-1 addr-bytes-2 x86)
  (if (endp addr-bytes-1)
      x86
    (wb-splits-ind-hint
     (cdr addr-bytes-1)
     addr-bytes-2
     (mv-nth 1 (wm08 (caar addr-bytes-1) (cdar addr-bytes-1) x86)))))

(defthmd wb-wb-split-reads-in-system-level-mode
  (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
                (all-paging-entries-found-p (strip-cars addr-bytes-1) (double-rewrite x86))
                (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                 (strip-cars addr-bytes-1) :w cpl (double-rewrite x86))
                (no-page-faults-during-translation-p
                 (strip-cars addr-bytes-1) :w cpl (double-rewrite x86))
                (addr-byte-alistp addr-bytes-1)
                (addr-byte-alistp addr-bytes-2))
           (equal (mv-nth 1 (wb addr-bytes-2 (mv-nth 1 (wb addr-bytes-1 x86))))
                  (mv-nth 1 (wb (append addr-bytes-1 addr-bytes-2) x86))))
  :hints (("Goal"
           :induct (wb-splits-ind-hint addr-bytes-1 addr-bytes-2 x86)
           :in-theory (e/d* (wb
                             all-paging-entries-found-p
                             mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                             no-page-faults-during-translation-p
                             acl2::list-fix)
                            (force (force))))))

;; ======================================================================

(defthmd rm08-from-linear-addresses-that-map-to-the-same-physical-address
  (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
                (equal
                 ;; The physical addresses corresponding to addr-1 and
                 ;; addr-2 are the same.
                 (mv-nth 1 (ia32e-entries-found-la-to-pa addr-1 r-w-x-1 cpl x86))
                 (mv-nth 1 (ia32e-entries-found-la-to-pa addr-2 r-w-x-2 cpl x86)))
                (paging-entries-found-p addr-1 (double-rewrite x86))
                (paging-entries-found-p addr-2 (double-rewrite x86))
                (pairwise-disjoint-p-aux
                 ;; The read isn't being done from the page tables.
                 (list (mv-nth 1 (ia32e-entries-found-la-to-pa addr-1 r-w-x-1 cpl x86)))
                 (open-qword-paddr-list-list (gather-all-paging-structure-qword-addresses x86)))
                (not (mv-nth 0 (ia32e-entries-found-la-to-pa addr-1 r-w-x-1 cpl x86)))
                (not (mv-nth 0 (ia32e-entries-found-la-to-pa addr-2 r-w-x-2 cpl x86))))
           (and
            (equal
             (mv-nth 0 (rm08 addr-1 r-w-x-1 x86))
             (mv-nth 0 (rm08 addr-2 r-w-x-2 x86)))
            (equal
             (mv-nth 1 (rm08 addr-1 r-w-x-1 x86))
             (mv-nth 1 (rm08 addr-2 r-w-x-2 x86)))
            (xlate-equiv-x86s
             (mv-nth 2 (rm08 addr-1 r-w-x-1 x86))
             (mv-nth 2 (rm08 addr-2 r-w-x-2 x86)))))
  :hints (("Goal" :in-theory (e/d* (rm08)
                                   (signed-byte-p
                                    unsigned-byte-p)))))

(defthmd wm08-from-linear-addresses-that-map-to-the-same-physical-address
  (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
                (equal
                 ;; The physical addresses corresponding to addr-1 and
                 ;; addr-2 are the same.
                 (mv-nth 1 (ia32e-entries-found-la-to-pa addr-1 :w cpl x86))
                 (mv-nth 1 (ia32e-entries-found-la-to-pa addr-2 :w cpl x86)))
                (paging-entries-found-p addr-1 (double-rewrite x86))
                (paging-entries-found-p addr-2 (double-rewrite x86))
                (pairwise-disjoint-p-aux
                 ;; The write isn't being done to the page tables.
                 (list (mv-nth 1 (ia32e-entries-found-la-to-pa addr-1 :w cpl x86)))
                 (open-qword-paddr-list-list (gather-all-paging-structure-qword-addresses x86)))
                (not (mv-nth 0 (ia32e-entries-found-la-to-pa addr-1 :w cpl x86)))
                (not (mv-nth 0 (ia32e-entries-found-la-to-pa addr-2 :w cpl x86))))
           (and
            (equal (mv-nth 0 (wm08 addr-1 val x86))
                   (mv-nth 0 (wm08 addr-2 val x86)))
            (xlate-equiv-x86s (mv-nth 1 (wm08 addr-1 val x86))
                              (mv-nth 1 (wm08 addr-2 val x86)))))
  :hints (("Goal" :in-theory (e/d* (wm08)
                                   (signed-byte-p
                                    unsigned-byte-p)))))

;; ======================================================================

(define translate-all-l-addrs (l-addrs r-w-x cpl x86)
  :guard (and (canonical-address-listp l-addrs)
              (member r-w-x '(:r :w :x))
              (unsigned-byte-p 2 cpl))
  :enabled t
  :non-executable t
  (if (endp l-addrs)
      nil
    (b* (((mv ?flg p-addr x86)
          (ia32e-entries-found-la-to-pa (car l-addrs) r-w-x cpl x86))
         ;; ((when flg)
         ;;  nil)
         )
      (cons p-addr (translate-all-l-addrs (cdr l-addrs) r-w-x cpl x86))))
  ///
  (defthm translate-all-l-addrs-and-xlate-equiv-structures
    (implies (xlate-equiv-structures x86-1 x86-2)
             (equal (translate-all-l-addrs l-addrs r-w-x cpl x86-1)
                    (translate-all-l-addrs l-addrs r-w-x cpl x86-2)))
    :rule-classes :congruence)

  (defthm translate-all-l-addrs-and-cdr
    (equal (cdr (translate-all-l-addrs l-addrs r-w-x cpl x86))
           (translate-all-l-addrs (cdr l-addrs) r-w-x cpl x86)))

  (defthm translate-all-l-addrs-and-car
    (implies (consp l-addrs)
             (equal (car (translate-all-l-addrs l-addrs r-w-x cpl x86))
                    (mv-nth 1 (ia32e-entries-found-la-to-pa (car l-addrs) r-w-x cpl x86)))))

  (defthm consp-translate-all-l-addrs
    (equal (consp (translate-all-l-addrs l-addrs r-w-x cpl x86))
           (consp l-addrs)))

  (defthm len-of-translate-all-l-addrs
    (equal (len (translate-all-l-addrs l-addrs r-w-x cpl x86))
           (len l-addrs)))

  (defthm member-p-of-translate-all-l-addrs-implies-consp-l-addrs
    (implies (member-p e (translate-all-l-addrs l-addrs r-w-x cpl x86))
             (consp l-addrs))
    :rule-classes :forward-chaining)

  (defthm translate-all-l-addrs-when-len-l-addrs=0
    (implies (equal (len l-addrs) 0)
             (equal (translate-all-l-addrs l-addrs r-w-x cpl x86)
                    nil)))

  (defthm translate-all-l-addrs-member-p-lemma
    (implies (and (disjoint-p (translate-all-l-addrs l-addrs-1 r-w-x-1 cpl x86)
                              (translate-all-l-addrs l-addrs-2 r-w-x-2 cpl x86))
                  (member-p index l-addrs-1))
             (disjoint-p
              (list (mv-nth 1 (ia32e-entries-found-la-to-pa index r-w-x-1 cpl x86)))
              (translate-all-l-addrs l-addrs-2 r-w-x-2 cpl x86)))
    :hints (("Goal"
             :induct (translate-all-l-addrs l-addrs-1 r-w-x-1 cpl x86)
             :in-theory (e/d* (disjoint-p member-p) ())))))

;; ======================================================================

(defthmd rm08-wm08-disjoint-in-system-level-mode
  (implies (and (paging-entries-found-p addr-1 (double-rewrite x86))
                (paging-entries-found-p addr-2 (double-rewrite x86))
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
           (and
            (equal (mv-nth 0 (rm08 addr-1 r-w-x (mv-nth 1 (wm08 addr-2 val x86))))
                   (mv-nth 0 (rm08 addr-1 r-w-x x86)))
            (equal (mv-nth 1 (rm08 addr-1 r-w-x (mv-nth 1 (wm08 addr-2 val x86))))
                   (mv-nth 1 (rm08 addr-1 r-w-x x86)))))
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
  (implies (and (paging-entries-found-p addr-1 (double-rewrite x86))
                (paging-entries-found-p addr-2 (double-rewrite x86))
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
           (and
            (equal (mv-nth 0 (rm08 addr-1 r-w-x (mv-nth 1 (wm08 addr-2 val x86))))
                   nil)
            (equal (mv-nth 1 (rm08 addr-1 r-w-x (mv-nth 1 (wm08 addr-2 val x86))))
                   val)))
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

;; Proving rb-wb-disjoint-in-system-level-mode:

(local
 (defthm rm08-and-wb-disjoint-lemma
   (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
                 (paging-entries-found-p index (double-rewrite x86))
                 (all-paging-entries-found-p (strip-cars addr-bytes) (double-rewrite x86))
                 (disjoint-p
                  ;; The physical addresses corresponding to index and
                  ;; (strip-cars addr-bytes) are different.
                  (list (mv-nth 1 (ia32e-entries-found-la-to-pa index r-w-x cpl x86)))
                  (translate-all-l-addrs (strip-cars addr-bytes) :w cpl (double-rewrite x86)))
                 (pairwise-disjoint-p-aux
                  ;; The read isn't being done from the page tables.
                  (list (mv-nth 1 (ia32e-entries-found-la-to-pa index r-w-x cpl x86)))
                  (open-qword-paddr-list-list
                   (gather-all-paging-structure-qword-addresses x86)))
                 (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                  ;; The write isn't being done to the page tables.
                  (strip-cars addr-bytes) :w cpl (double-rewrite x86)))
            (and
             (equal (mv-nth 0 (rm08 index r-w-x (mv-nth 1 (wb addr-bytes x86))))
                    (mv-nth 0 (rm08 index r-w-x x86)))
             (equal (mv-nth 1 (rm08 index r-w-x (mv-nth 1 (wb addr-bytes x86))))
                    (mv-nth 1 (rm08 index r-w-x x86)))))
   :hints (("Goal"
            :induct (wb-ind-hint addr-bytes x86)
            :in-theory (e/d* (wb
                              rm08-wm08-disjoint-in-system-level-mode
                              all-paging-entries-found-p
                              mapped-lin-addrs-disjoint-from-paging-structure-addrs-p)
                             ()))
           ("Subgoal *1/2"
            :use ((:instance gather-all-paging-structure-qword-addresses-with-xlate-equiv-structures
                             (x86 x86)
                             (x86-equiv (mv-nth 1 (wm08 (car (strip-cars addr-bytes)) (car (strip-cdrs addr-bytes)) x86)))))
            :in-theory (e/d* (wb
                              rm08-wm08-disjoint-in-system-level-mode
                              all-paging-entries-found-p
                              mapped-lin-addrs-disjoint-from-paging-structure-addrs-p)
                             ())))))

(defun-nx rb-1-wb-disjoint-ind-hint
  (l-addrs-1 l-addrs-2 bytes r-w-x x86 acc)
  (if (endp l-addrs-1)
      acc
    (rb-1-wb-disjoint-ind-hint
     (cdr l-addrs-1) l-addrs-2 bytes r-w-x
     (mv-nth 2 (rm08 (car l-addrs-1) r-w-x x86))
     (append acc (list (mv-nth 1 (rm08 (car l-addrs-1) r-w-x x86)))))))

(local
 (defthm relating-rm08-and-rb-1-error
   (implies (mv-nth 0 (rm08 (car l-addrs) r-w-x x86))
            (equal (mv-nth 1 (rb-1 l-addrs r-w-x x86 acc))
                   acc))))

#||
(MV-NTH 1
        (RB-1 (CDR L-ADDRS-1)
              R-W-X
              (MV-NTH 1
                      (WB ADDR-BYTES
                          (MV-NTH 2 (RM08 (CAR L-ADDRS-1) R-W-X X86))))
              NIL))

==

(MV-NTH
 1
 (RB-1 (CDR L-ADDRS-1) R-W-X
       (MV-NTH 2 (RM08 (CAR L-ADDRS-1) R-W-X
                       (MV-NTH 1 (WB ADDR-BYTES X86)))) NIL))

----------------------------------------------------------------------

L.H.S.:

The congruence rule mv-nth-1-rb-and-xlate-equiv-x86s-disjoint says
that in the x86 position of rb-1, we need preserve only
xlate-equiv-x86s.

So, if we apply the rewrite rule
mv-nth-1-wb-and-xlate-equiv-x86s-disjoint to the following:

(MV-NTH 1 (WB ADDR-BYTES (MV-NTH 2 (RM08 (CAR L-ADDRS-1) R-W-X X86))))

we will get (also using the rewrite rule mv-nth-2-rm08-and-xlate-equiv-x86s):

(MV-NTH 1 (WB ADDR-BYTES x86))

----------------------------------------------------------------------

R.H.S.:

Again, the congruence rule mv-nth-1-rb-and-xlate-equiv-x86s-disjoint
says that in the x86 position of rb-1, we need preserve only
xlate-equiv-x86s.

So, if we apply the rewrite rule mv-nth-2-rm08-and-xlate-equiv-x86s to
the following:

(MV-NTH 2 (RM08 (CAR L-ADDRS-1) R-W-X (MV-NTH 1 (WB ADDR-BYTES X86))))

we will get:

(MV-NTH 1 (WB ADDR-BYTES X86))

(XLATE-EQUIV-X86S
 (MV-NTH 2 (RM08 (CAR L-ADDRS-1) R-W-X (MV-NTH 1 (WB ADDR-BYTES X86))))
 (MV-NTH 1 (WB ADDR-BYTES X86)))

----------------------------------------------------------------------

||#

(local
 (defthmd rb-1-wb-disjoint-in-system-level-mode-helper
   (implies
    (and
     (consp l-addrs-1)
     (equal
      (mv-nth 1
              (rb-1
               (cdr l-addrs-1)
               r-w-x
               (mv-nth 1 (wb addr-bytes (mv-nth 2 (rm08 (car l-addrs-1) r-w-x x86))))
               nil))
      (mv-nth 1 (rb-1 (cdr l-addrs-1) r-w-x x86 nil)))
     (paging-entries-found-p (car l-addrs-1) x86)
     (all-paging-entries-found-p (cdr l-addrs-1) x86)
     (all-paging-entries-found-p (strip-cars addr-bytes) x86)
     (disjoint-p
      (translate-all-l-addrs l-addrs-1 r-w-x
                             (loghead 2 (xr :seg-visible 1 x86))
                             x86)
      (translate-all-l-addrs (strip-cars addr-bytes)
                             :w (loghead 2 (xr :seg-visible 1 x86))
                             x86))
     (pairwise-disjoint-p-aux
      (list
       (mv-nth
        1
        (ia32e-entries-found-la-to-pa
         (car l-addrs-1) r-w-x (loghead 2 (xr :seg-visible 1 x86)) x86)))
      (open-qword-paddr-list-list
       (gather-all-paging-structure-qword-addresses x86)))
     (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
      (cdr l-addrs-1) r-w-x (loghead 2 (xr :seg-visible 1 x86)) x86)
     (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
      (strip-cars addr-bytes) :w (loghead 2 (xr :seg-visible 1 x86)) x86)
     (not (mv-nth 0 (rm08 (car l-addrs-1) r-w-x x86))))
    (equal (mv-nth 1 (rb-1 l-addrs-1 r-w-x (mv-nth 1 (wb addr-bytes x86)) nil))
           (cons (mv-nth 1 (rm08 (car l-addrs-1) r-w-x x86))
                 (mv-nth 1 (rb-1 (cdr l-addrs-1) r-w-x x86 nil)))))
   :hints (("Goal" :in-theory (e/d* (disjoint-p)
                                    (mv-nth-1-rb-1-and-xlate-equiv-x86s-disjoint))
            :use
            ((:instance mv-nth-1-rb-1-and-xlate-equiv-x86s-disjoint
                        (l-addrs (cdr l-addrs-1))
                        (r-w-x r-w-x)
                        (x86-1 (mv-nth 2
                                       (rm08 (car l-addrs-1)
                                             r-w-x (mv-nth 1 (wb addr-bytes x86)))))
                        (x86-2 (mv-nth 1 (wb addr-bytes x86)))
                        (acc nil))
             (:instance mv-nth-1-rb-1-and-xlate-equiv-x86s-disjoint
                        (l-addrs (cdr l-addrs-1))
                        (r-w-x r-w-x)
                        (x86-1 (mv-nth 1
                                       (wb addr-bytes
                                           (mv-nth 2 (rm08 (car l-addrs-1) r-w-x x86)))))
                        (x86-2 (mv-nth 1 (wb addr-bytes x86)))
                        (acc nil)))))))

(local
 (defthmd rb-1-wb-disjoint-in-system-level-mode-error
   (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
                 (all-paging-entries-found-p l-addrs-1 (double-rewrite x86))
                 (all-paging-entries-found-p (strip-cars addr-bytes) (double-rewrite x86))
                 (disjoint-p
                  ;; the physical addresses corresponding to l-addrs-1
                  ;; and (strip-cars addr-bytes) are different.
                  (translate-all-l-addrs l-addrs-1 r-w-x cpl (double-rewrite x86))
                  (translate-all-l-addrs (strip-cars addr-bytes) :w cpl (double-rewrite x86)))
                 (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                  ;; the read isn't being done from the page tables.
                  l-addrs-1 r-w-x cpl (double-rewrite x86))
                 (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                  ;; the write isn't being done to the page tables.
                  (strip-cars addr-bytes) :w cpl (double-rewrite x86)))
            (equal (mv-nth 0 (rb-1 l-addrs-1 r-w-x (mv-nth 1 (wb addr-bytes x86)) acc))
                   (mv-nth 0 (rb-1 l-addrs-1 r-w-x x86 acc))))
   :hints (("Goal"
            :induct (rb-1-wb-disjoint-ind-hint l-addrs-1 (strip-cars addr-bytes) bytes r-w-x x86 acc)
            :in-theory (e/d* (rb-1
                              rb-1-wb-disjoint-in-system-level-mode-helper
                              wb
                              rm08-wm08-disjoint-in-system-level-mode
                              all-paging-entries-found-p
                              mapped-lin-addrs-disjoint-from-paging-structure-addrs-p)
                             (signed-byte-p
                              unsigned-byte-p
                              mv-nth-0-rb-1-and-xlate-equiv-x86s-disjoint)))
           ("Subgoal *1/2.5"
            :in-theory (e/d* (rb-1
                              rb-1-wb-disjoint-in-system-level-mode-helper
                              wb
                              rm08-wm08-disjoint-in-system-level-mode
                              all-paging-entries-found-p
                              mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                              disjoint-p)
                             (mv-nth-0-rb-1-and-xlate-equiv-x86s-disjoint
                              signed-byte-p
                              unsigned-byte-p
                              relating-rm08-and-rb-1-error))
            :use ((:instance relating-rm08-and-rb-1-error
                             (x86 (mv-nth 1 (wb addr-bytes x86)))
                             (l-addrs l-addrs-1)
                             (r-w-x r-w-x)
                             (acc acc))))
           ("Subgoal *1/2.4"
            :expand (rb-1 l-addrs-1 r-w-x (mv-nth 1 (wb addr-bytes x86)) acc)
            :use ((:instance mv-nth-0-rb-1-and-xlate-equiv-x86s-disjoint
                             (l-addrs (cdr l-addrs-1))
                             (r-w-x r-w-x)
                             (x86-1 (mv-nth 2 (rm08 (car l-addrs-1) r-w-x (mv-nth 1 (wb addr-bytes x86)))))
                             (x86-2 (mv-nth 1 (wb addr-bytes x86)))
                             (acc (append acc (list (mv-nth 1 (rm08 (car l-addrs-1) r-w-x (mv-nth 1 (wb addr-bytes x86))))))))
                  (:instance mv-nth-0-rb-1-and-xlate-equiv-x86s-disjoint
                             (l-addrs (cdr l-addrs-1))
                             (r-w-x r-w-x)
                             (x86-1 (mv-nth 1 (wb addr-bytes (mv-nth 2 (rm08 (car l-addrs-1) r-w-x x86)))))
                             (x86-2 (mv-nth 1 (wb addr-bytes x86)))
                             (acc (append acc (list (mv-nth 1 (rm08 (car l-addrs-1) r-w-x x86)))))))
            :in-theory (e/d* (rb-1
                              rb-1-wb-disjoint-in-system-level-mode-helper
                              wb
                              rm08-wm08-disjoint-in-system-level-mode
                              all-paging-entries-found-p
                              mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                              disjoint-p)
                             (mv-nth-0-rb-1-and-xlate-equiv-x86s-disjoint
                              mv-nth-1-rb-1-and-xlate-equiv-x86s-disjoint
                              signed-byte-p
                              unsigned-byte-p
                              relating-rm08-and-rb-1-error))))))

(defthm rb-wb-disjoint-in-system-level-mode-error
  (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
                (all-paging-entries-found-p l-addrs-1 (double-rewrite x86))
                (all-paging-entries-found-p (strip-cars addr-bytes) (double-rewrite x86))
                (disjoint-p
                 ;; The physical addresses corresponding to l-addrs-1
                 ;; and (strip-cars addr-bytes) are different.
                 (translate-all-l-addrs l-addrs-1 r-w-x cpl (double-rewrite x86))
                 (translate-all-l-addrs (strip-cars addr-bytes) :w cpl (double-rewrite x86)))
                (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                 ;; The read isn't being done from the page tables.
                 l-addrs-1 r-w-x cpl (double-rewrite x86))
                (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                 ;; The write isn't being done to the page tables.
                 (strip-cars addr-bytes) :w cpl (double-rewrite x86)))
           (equal (mv-nth 0 (rb l-addrs-1 r-w-x (mv-nth 1 (wb addr-bytes x86))))
                  (mv-nth 0 (rb l-addrs-1 r-w-x x86))))
  :hints (("Goal"
           :use ((:instance rb-1-wb-disjoint-in-system-level-mode-error
                            (acc nil)))
           :in-theory (e/d* (rb)
                            (mv-nth-0-rb-1-and-xlate-equiv-x86s-disjoint
                             signed-byte-p unsigned-byte-p rb-1)))))

(defthmd rb-1-wb-disjoint-in-system-level-mode
  (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
                (all-paging-entries-found-p l-addrs-1 (double-rewrite x86))
                (all-paging-entries-found-p (strip-cars addr-bytes) (double-rewrite x86))
                (disjoint-p
                 ;; The physical addresses corresponding to l-addrs-1
                 ;; and (strip-cars addr-bytes) are different.
                 (translate-all-l-addrs l-addrs-1 r-w-x cpl (double-rewrite x86))
                 (translate-all-l-addrs (strip-cars addr-bytes) :w cpl (double-rewrite x86)))
                (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                 ;; The read isn't being done from the page tables.
                 l-addrs-1 r-w-x cpl (double-rewrite x86))
                (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                 ;; The write isn't being done to the page tables.
                 (strip-cars addr-bytes) :w cpl (double-rewrite x86))
                (true-listp acc))
           (equal (mv-nth 1 (rb-1 l-addrs-1 r-w-x (mv-nth 1 (wb addr-bytes x86)) acc))
                  (mv-nth 1 (rb-1 l-addrs-1 r-w-x x86 acc))))
  :hints (("Goal"
           :induct (rb-1-wb-disjoint-ind-hint l-addrs-1 (strip-cars addr-bytes) bytes r-w-x x86 acc)
           :in-theory (e/d* (rb-1
                             rb-1-wb-disjoint-in-system-level-mode-helper
                             wb
                             rm08-wm08-disjoint-in-system-level-mode
                             all-paging-entries-found-p
                             mapped-lin-addrs-disjoint-from-paging-structure-addrs-p)
                            (signed-byte-p unsigned-byte-p)))
          ("Subgoal *1/2.4'"
           :in-theory (e/d* (rb-1
                             rb-1-wb-disjoint-in-system-level-mode-helper
                             wb
                             rm08-wm08-disjoint-in-system-level-mode
                             all-paging-entries-found-p
                             mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                             disjoint-p)
                            (signed-byte-p
                             unsigned-byte-p
                             relating-rm08-and-rb-1-error))
           :use ((:instance relating-rm08-and-rb-1-error
                            (x86 (mv-nth 1 (wb addr-bytes x86)))
                            (l-addrs l-addrs-1)
                            (r-w-x r-w-x)
                            (acc acc))))))

(defthm rb-wb-disjoint-in-system-level-mode
  (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
                (all-paging-entries-found-p l-addrs-1 (double-rewrite x86))
                (all-paging-entries-found-p (strip-cars addr-bytes) (double-rewrite x86))
                (disjoint-p
                 ;; The physical addresses corresponding to l-addrs-1
                 ;; and (strip-cars addr-bytes) are different.
                 (translate-all-l-addrs l-addrs-1 r-w-x cpl (double-rewrite x86))
                 (translate-all-l-addrs (strip-cars addr-bytes) :w cpl (double-rewrite x86)))
                (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                 ;; The read isn't being done from the page tables.
                 l-addrs-1 r-w-x cpl (double-rewrite x86))
                (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                 ;; The write isn't being done to the page tables.
                 (strip-cars addr-bytes) :w cpl (double-rewrite x86))
                (addr-byte-alistp addr-bytes))
           (equal (mv-nth 1 (rb l-addrs-1 r-w-x (mv-nth 1 (wb addr-bytes x86))))
                  (mv-nth 1 (rb l-addrs-1 r-w-x x86))))
  :hints (("Goal"
           :in-theory (e/d* (rb rb-1-wb-disjoint-in-system-level-mode)
                            (rb-1 signed-byte-p unsigned-byte-p force (force))))))

(defthm program-at-wb-disjoint-in-system-level-mode
  ;; Follows directly from rb-wb-disjoint-in-system-level-mode and
  ;; rb-wb-disjoint-in-system-level-mode-error.
  (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
                (all-paging-entries-found-p l-addrs (double-rewrite x86))
                (all-paging-entries-found-p (strip-cars addr-bytes) (double-rewrite x86))
                (disjoint-p
                 ;; The physical addresses corresponding to l-addrs
                 ;; and (strip-cars addr-bytes) are different.
                 (translate-all-l-addrs l-addrs :x cpl (double-rewrite x86))
                 (translate-all-l-addrs (strip-cars addr-bytes) :w cpl (double-rewrite x86)))
                (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                 ;; The read isn't being done from the page tables.
                 l-addrs :x cpl (double-rewrite x86))
                (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                 ;; The write isn't being done to the page tables.
                 (strip-cars addr-bytes) :w cpl (double-rewrite x86))
                (addr-byte-alistp addr-bytes))
           (equal (program-at l-addrs bytes (mv-nth 1 (wb addr-bytes x86)))
                  (program-at l-addrs bytes x86)))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance rb-wb-disjoint-in-system-level-mode
                            (l-addrs-1 l-addrs)
                            (r-w-x :x)
                            (addr-bytes addr-bytes)
                            (x86 x86)))
           :in-theory (e/d (program-at)
                           (rb-wb-disjoint-in-system-level-mode)))))

(defthm program-at-pop-x86-oracle-in-system-level-mode
  (implies (case-split (not (programmer-level-mode x86)))
           (equal (program-at addresses r-w-x (mv-nth 1 (pop-x86-oracle x86)))
                  (program-at addresses r-w-x x86)))
  :hints (("Goal" :in-theory (e/d (program-at pop-x86-oracle pop-x86-oracle-logic)
                                  (rb)))))

(defthm program-at-!flgi-in-system-level-mode
  (implies (case-split (not (programmer-level-mode x86)))
           (equal (program-at addresses r-w-x (!flgi flg val x86))
                  (program-at addresses r-w-x x86)))
  :hints (("Goal" :in-theory (e/d (program-at !flgi)
                                  (force (force))))))

(defthm program-at-!flgi-undefined-in-system-level-mode
  (implies (case-split (not (programmer-level-mode x86)))
           (equal (program-at addresses r-w-x (!flgi-undefined flg x86))
                  (program-at addresses r-w-x x86)))
  :hints (("Goal" :in-theory (e/d (program-at !flgi !flgi-undefined)
                                  (force (force))))))

(defthm program-at-write-user-rflags-in-system-level-mode
  (implies (case-split (not (programmer-level-mode x86)))
           (equal (program-at addresses r-w-x (write-user-rflags flags mask x86))
                  (program-at addresses r-w-x x86)))
  :hints (("Goal" :in-theory (e/d (write-user-rflags)
                                  (force (force))))))

;; ======================================================================

;; Proving rb-wb-subset-in-system-level-mode:

(defun-nx rm08-and-wb-member-lemma-ind-hint
  (index addr-bytes r-w-x cpl x86)
  (if (endp addr-bytes)
      (mv 0 0 x86)
    (if (equal
         (mv-nth 1 (ia32e-entries-found-la-to-pa index r-w-x cpl x86))
         (mv-nth 1 (ia32e-entries-found-la-to-pa (car (strip-cars addr-bytes)) :w cpl x86)))

        (mv (car (strip-cars addr-bytes))
            (car (strip-cdrs addr-bytes))
            (mv-nth 1 (wm08 (car (strip-cars addr-bytes)) (car (strip-cdrs addr-bytes)) x86)))

      (rm08-and-wb-member-lemma-ind-hint
       index
       (cdr addr-bytes)
       r-w-x
       cpl
       (mv-nth 1 (wm08 (car (strip-cars addr-bytes)) (car (strip-cdrs addr-bytes)) x86))))))

(local
 (defthm rm08-and-wb-member-lemma-for-error-field
   (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
                 (paging-entries-found-p index (double-rewrite x86))
                 (all-paging-entries-found-p (strip-cars addr-bytes) (double-rewrite x86))
                 (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                  (strip-cars addr-bytes) :w cpl (double-rewrite x86))
                 (not (mv-nth 0 (ia32e-entries-found-la-to-pa index r-w-x cpl x86)))
                 (no-page-faults-during-translation-p
                  (strip-cars addr-bytes) :w cpl (double-rewrite x86)))
            (equal (mv-nth 0 (rm08 index r-w-x (mv-nth 1 (wb addr-bytes x86))))
                   nil))
   :hints (("Goal"
            :induct (rm08-and-wb-member-lemma-ind-hint index addr-bytes r-w-x cpl x86)
            :in-theory (e/d* (wb
                              rm08
                              rm08-wm08-disjoint-in-system-level-mode
                              rm08-wm08-equal-in-system-level-mode
                              all-paging-entries-found-p
                              no-page-faults-during-translation-p
                              mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                              member-p)
                             ())))))

;; (defthm strip-cdrs-of-rev-is-rev-of-strip-cdrs
;;   ;; strip-cars-of-rev-is-rev-of-strip-cars already exists.
;;   (equal (strip-cdrs (acl2::rev as))
;;          (acl2::rev (strip-cdrs as))))

;; (defthm translate-all-l-addrs-of-rev-is-rev-of-translate-all-l-addrs
;;   (equal (translate-all-l-addrs (acl2::rev l-addrs) r-w-x cpl x86)
;;          (acl2::rev (translate-all-l-addrs l-addrs r-w-x cpl x86))))

;; (defun-nx rm08-and-wb-member-lemma-ind-hint-value
;;   (index addr-bytes r-w-x cpl x86)

;;   (if (endp addr-bytes)
;;       (mv 0 0 x86)

;;     (if (equal
;;          ;; If the physical addresses corresponding to index and the
;;          ;; first address of addr-bytes are the same:
;;          (mv-nth 1 (ia32e-entries-found-la-to-pa index r-w-x cpl x86))
;;          (mv-nth 1 (ia32e-entries-found-la-to-pa (car (strip-cars addr-bytes)) :w cpl x86)))

;;         (if
;;             ;; If the physical address corresponding to index is
;;             ;; unique, i.e., no linear address in (cdr addr-bytes)
;;             ;; maps to the same physical address as index: note that
;;             ;; this covers the case of duplicate linear addresses
;;             ;; too.
;;             (not
;;              (member-p
;;               (mv-nth 1 (ia32e-entries-found-la-to-pa index r-w-x cpl x86))
;;               (translate-all-l-addrs (strip-cars (cdr addr-bytes)) :w cpl x86)))

;;             (mv (car (strip-cars addr-bytes))
;;                 (car (strip-cdrs addr-bytes))
;;                 (mv-nth 1 (wm08 (car (strip-cars addr-bytes)) (car (strip-cdrs addr-bytes)) x86)))

;;           ;; The physical address corresponding to index is not
;;           ;; unique, so the byte corresponding to the first match will
;;           ;; not be the final value of the memory location pointed to
;;           ;; by index.
;;           (b* ((pos-of-final-match
;;                 (pos
;;                  (mv-nth 1 (ia32e-entries-found-la-to-pa index r-w-x cpl x86))
;;                  (acl2::rev (translate-all-l-addrs (strip-cars (cdr addr-bytes)) :w cpl x86))))
;;                (final-match-addr
;;                 (nth
;;                  pos-of-final-match
;;                  (acl2::rev (translate-all-l-addrs (strip-cars (cdr addr-bytes)) :w cpl x86))))
;;                (final-match-byte
;;                 (nth
;;                  pos-of-final-match
;;                  (acl2::rev (strip-cdrs (cdr addr-bytes))))))

;;             (mv final-match-addr
;;                 final-match-byte
;;                 (mv-nth 1 (wm08 final-match-addr final-match-byte
;;                                 (mv-nth 1 (wb <all-the-writes-preceding-final-match> x86)))))))

;;       (rm08-and-wb-member-lemma-ind-hint-value
;;        index
;;        (cdr addr-bytes)
;;        r-w-x
;;        cpl
;;        (mv-nth 1 (wm08 (car (strip-cars addr-bytes)) (car (strip-cdrs addr-bytes)) x86))))))


;; (local
;;  (defthm rm08-and-wb-member-lemma
;;    ;; '((0 . A) (1 . B) (0 . X) (2 . D))
;;    ;; (nth (pos 0 (reverse '(0 1 0 2))) (reverse '(A B X D)))
;;    (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
;;                  (paging-entries-found-p index (double-rewrite x86))
;;                  (all-paging-entries-found-p (strip-cars addr-bytes) (double-rewrite x86))
;;                  (member-p
;;                   ;; The physical addresses corresponding to index is
;;                   ;; a member of those corresponding to (strip-cars addr-bytes).
;;                   (mv-nth 1 (ia32e-entries-found-la-to-pa index r-w-x cpl x86))
;;                   (translate-all-l-addrs (strip-cars addr-bytes) :w cpl (double-rewrite x86)))
;;                  ;; Note that the following two hypotheses about
;;                  ;; uniqueness of linear and physical addresses means
;;                  ;; that I need a "wb-remove-duplicate-writes" kinda
;;                  ;; theorem about wb in the system-level mode.
;;                  ;; (no-duplicates-p
;;                  ;;  ;; All physical addresses being written to are
;;                  ;;  ;; unique.
;;                  ;;  (translate-all-l-addrs (strip-cars addr-bytes) :w cpl (double-rewrite x86)))
;;                  ;; (no-duplicates-p
;;                  ;;  ;; All linear addresses being written to are unique.
;;                  ;;  (strip-cars addr-bytes))
;;                  (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
;;                   ;; The write isn't being done to the page tables.
;;                   (strip-cars addr-bytes) :w cpl (double-rewrite x86))
;;                  ;; Can I not remove the following hyp?
;;                  (not (mv-nth 0 (ia32e-entries-found-la-to-pa index r-w-x cpl x86)))
;;                  (no-page-faults-during-translation-p
;;                   ;; If the write doesn't succeed, the read can't read
;;                   ;; what was written, duh.
;;                   (strip-cars addr-bytes) :w cpl (double-rewrite x86))
;;                  (equal (len (strip-cars addr-bytes)) (len (strip-cdrs addr-bytes)))
;;                  (addr-byte-alistp addr-bytes))
;;             (equal (mv-nth 1 (rm08 index r-w-x (mv-nth 1 (wb addr-bytes x86))))
;;                    (nth
;;                     (pos
;;                      (mv-nth 1 (ia32e-entries-found-la-to-pa index r-w-x cpl x86))
;;                      (reverse (translate-all-l-addrs (strip-cars addr-bytes) :w cpl (double-rewrite x86))))
;;                     (reverse (strip-cdrs addr-bytes)))))
;;    :hints (("Goal"
;;             :induct (rm08-and-wb-member-lemma-ind-hint index (reverse addr-bytes) r-w-x cpl x86)
;;             :in-theory (e/d* (wb
;;                               rm08-wm08-disjoint-in-system-level-mode
;;                               rm08-wm08-equal-in-system-level-mode
;;                               all-paging-entries-found-p
;;                               no-page-faults-during-translation-p
;;                               mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
;;                               member-p)
;;                              ()))
;;            ("Subgoal *1/2" :expand (wb addr-bytes x86)
;;             :in-theory (e/d* (pos
;;                               rm08-wm08-disjoint-in-system-level-mode
;;                               rm08-wm08-equal-in-system-level-mode
;;                               no-page-faults-during-translation-p)
;;                              ())))))


(defthm uniqueness-of-physical-address-implies-that-of-linear-address
  (implies
   (not
    ;; Physical addresses corresponding to lin-addr-1 and
    ;; lin-addr-2 are different.
    (equal (mv-nth 1 (ia32e-entries-found-la-to-pa lin-addr-1 r-w-x cpl x86))
           (mv-nth 1 (ia32e-entries-found-la-to-pa lin-addr-2 r-w-x cpl x86))))
   (not (equal lin-addr-1 lin-addr-2)))
  :rule-classes nil)

(defthmd uniqueness-of-physical-addresses-implies-that-of-linear-addresses-aux
  (implies (not (member-p (mv-nth 1 (ia32e-entries-found-la-to-pa lin-addr r-w-x cpl x86))
                          (translate-all-l-addrs l-addrs r-w-x cpl x86)))
           (not (member-p lin-addr l-addrs)))
  :hints (("Goal"
           :in-theory (e/d* (member-p
                             no-duplicates-p
                             translate-all-l-addrs)
                            ()))))

(defthm uniqueness-of-physical-addresses-implies-that-of-linear-addresses
  (implies (no-duplicates-p
            ;; All physical addresses being written to are unique.
            (translate-all-l-addrs l-addrs r-w-x cpl (double-rewrite x86)))
           (no-duplicates-p l-addrs))
  :hints (("Goal"
           :in-theory (e/d* (uniqueness-of-physical-addresses-implies-that-of-linear-addresses-aux)
                            ())))
  :rule-classes (:rewrite :forward-chaining))

(defthmd consp-strip-cdrs
  (implies (consp as)
           (consp (strip-cdrs as)))
  :rule-classes (:rewrite :type-prescription))

(local
 (defthmd rm08-and-wb-member-lemma-helper
   (implies
    (and
     (equal cpl (loghead 2 (xr :seg-visible 1 x86)))
     (consp addr-bytes)
     (equal
      (mv-nth 1 (ia32e-entries-found-la-to-pa index r-w-x cpl x86))
      (mv-nth 1 (ia32e-entries-found-la-to-pa (car (strip-cars addr-bytes)) :w cpl x86)))
     (paging-entries-found-p index x86)
     (all-paging-entries-found-p (strip-cars addr-bytes) x86)
     (consp (strip-cars addr-bytes))
     (no-duplicates-p (translate-all-l-addrs (strip-cars addr-bytes) :w cpl x86))
     (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
      (strip-cars addr-bytes) :w cpl x86)
     (not (mv-nth 0 (ia32e-entries-found-la-to-pa index r-w-x cpl x86)))
     (no-page-faults-during-translation-p (strip-cars addr-bytes) :w cpl x86)
     (addr-byte-alistp addr-bytes)
     (consp (strip-cdrs addr-bytes)))
    (equal (mv-nth 1 (rm08 index r-w-x (mv-nth 1 (wb addr-bytes x86))))
           (car (strip-cdrs addr-bytes))))
   :hints (("Goal"
            :do-not-induct t
            :expand (wb addr-bytes x86)
            :in-theory (e/d* (no-page-faults-during-translation-p
                              mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                              all-paging-entries-found-p
                              pos rm08-wm08-equal-in-system-level-mode
                              disjoint-p)
                             (rm08-from-linear-addresses-that-map-to-the-same-physical-address
                              rm08-and-wb-disjoint-lemma
                              uniqueness-of-physical-addresses-implies-that-of-linear-addresses))
            :use ((:instance rm08-and-wb-disjoint-lemma
                             (index index)
                             (r-w-x r-w-x)
                             (addr-bytes (cdr addr-bytes))
                             (x86 (mv-nth 1
                                          (wm08 (car (car addr-bytes))
                                                (cdr (car addr-bytes))
                                                x86)))
                             (cpl (bitops::part-select-width-low
                                   (seg-visiblei
                                    1
                                    (mv-nth 1 (wm08 (car (car addr-bytes)) (cdr (car addr-bytes)) x86)))
                                   2 0)))
                  (:instance gather-all-paging-structure-qword-addresses-with-xlate-equiv-structures
                             (x86 (mv-nth 1 (wm08 (car (car addr-bytes)) (cdr (car addr-bytes)) x86)))
                             (x86-equiv x86))
                  (:instance uniqueness-of-physical-addresses-implies-that-of-linear-addresses
                             (l-addrs (strip-cars addr-bytes))
                             (r-w-x :w)
                             (cpl (loghead 2 (xr :seg-visible 1 x86)))
                             (x86 x86))
                  (:instance consp-strip-cdrs
                             (as addr-bytes)))))))


(local
 (defthm rm08-and-wb-member-lemma
   (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
                 (paging-entries-found-p index (double-rewrite x86))
                 (all-paging-entries-found-p (strip-cars addr-bytes) (double-rewrite x86))
                 (member-p
                  ;; The physical addresses corresponding to index is
                  ;; a member of those corresponding to (strip-cars addr-bytes).
                  (mv-nth 1 (ia32e-entries-found-la-to-pa index r-w-x cpl x86))
                  (translate-all-l-addrs (strip-cars addr-bytes) :w cpl (double-rewrite x86)))
                 ;; Note that the following two hypotheses about
                 ;; uniqueness of linear and physical addresses means
                 ;; that I need a "wb-remove-duplicate-writes" kinda
                 ;; theorem about wb in the system-level mode.
                 (no-duplicates-p
                  ;; All physical addresses being written to are
                  ;; unique.
                  (translate-all-l-addrs (strip-cars addr-bytes) :w cpl (double-rewrite x86)))
                 (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                  ;; The write isn't being done to the page tables.
                  (strip-cars addr-bytes) :w cpl (double-rewrite x86))
                 (not (mv-nth 0 (ia32e-entries-found-la-to-pa index r-w-x cpl x86)))
                 (no-page-faults-during-translation-p
                  ;; If the write doesn't succeed, the read can't read
                  ;; what was written, duh.
                  (strip-cars addr-bytes) :w cpl (double-rewrite x86))
                 (equal (len (strip-cars addr-bytes)) (len (strip-cdrs addr-bytes)))
                 (addr-byte-alistp addr-bytes))
            (equal (mv-nth 1 (rm08 index r-w-x (mv-nth 1 (wb addr-bytes x86))))
                   (nth
                    (pos
                     (mv-nth 1 (ia32e-entries-found-la-to-pa index r-w-x cpl x86))
                     (translate-all-l-addrs (strip-cars addr-bytes) :w cpl (double-rewrite x86)))
                    (strip-cdrs addr-bytes))))
   :hints (("Goal"
            :induct (rm08-and-wb-member-lemma-ind-hint index addr-bytes r-w-x cpl x86)
            :in-theory (e/d* (wb
                              rm08-wm08-disjoint-in-system-level-mode
                              rm08-wm08-equal-in-system-level-mode
                              all-paging-entries-found-p
                              no-page-faults-during-translation-p
                              mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                              member-p
                              pos
                              rm08-and-wb-member-lemma-helper)
                             ())))))

(local
 (defthmd rb-1-wb-subset-in-system-level-mode-helper
   (implies
    (and (consp l-addrs-1)
         (paging-entries-found-p (car l-addrs-1) x86)
         (all-paging-entries-found-p (cdr l-addrs-1) x86)
         (all-paging-entries-found-p (strip-cars addr-bytes) x86)
         (member-p
          (mv-nth 1 (ia32e-entries-found-la-to-pa
                     (car l-addrs-1) r-w-x (loghead 2 (xr :seg-visible 1 x86)) x86))
          (translate-all-l-addrs (strip-cars addr-bytes)
                                 :w (loghead 2 (xr :seg-visible 1 x86)) x86))
         (no-duplicates-p
          (translate-all-l-addrs
           (strip-cars addr-bytes) :w (loghead 2 (xr :seg-visible 1 x86)) x86))
         (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
          (strip-cars addr-bytes) :w (loghead 2 (xr :seg-visible 1 x86)) x86)
         (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
          (cdr l-addrs-1) r-w-x (loghead 2 (xr :seg-visible 1 x86)) x86)
         (not
          (mv-nth 0
                  (ia32e-entries-found-la-to-pa
                   (car l-addrs-1) r-w-x (loghead 2 (xr :seg-visible 1 x86)) x86)))
         (no-page-faults-during-translation-p
          (strip-cars addr-bytes) :w (loghead 2 (xr :seg-visible 1 x86)) x86)
         (addr-byte-alistp addr-bytes))
    (equal
     (mv-nth 1 (rb-1 l-addrs-1 r-w-x (mv-nth 1 (wb addr-bytes x86)) nil))
     (cons
      (nth
       (pos
        (mv-nth
         1
         (ia32e-entries-found-la-to-pa
          (car l-addrs-1) r-w-x (loghead 2 (xr :seg-visible 1 x86)) x86))
        (translate-all-l-addrs (strip-cars addr-bytes) :w (loghead 2 (xr :seg-visible 1 x86)) x86))
       (strip-cdrs addr-bytes))
      (mv-nth 1
              (rb-1 (cdr l-addrs-1) r-w-x
                    (mv-nth 1 (wb addr-bytes (mv-nth 2 (rm08 (car l-addrs-1) r-w-x x86)))) nil)))))
   :hints (("Goal"
            :do-not-induct t
            :expand (rb-1 l-addrs-1 r-w-x (mv-nth 1 (wb addr-bytes x86)) nil)
            :in-theory (e/d* (no-page-faults-during-translation-p
                              mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                              all-paging-entries-found-p)
                             (mv-nth-1-wb-and-xlate-equiv-x86s-disjoint
                              ))
            :use ((:instance mv-nth-1-wb-and-xlate-equiv-x86s-disjoint
                             (x86-1 (mv-nth 2 (rm08 (car l-addrs-1) r-w-x x86)))
                             (x86-2 x86)
                             (addr-bytes addr-bytes))
                  (:instance mv-nth-1-rb-1-and-xlate-equiv-x86s-disjoint
                             (x86-1 (mv-nth 1 (wb addr-bytes (mv-nth 2 (rm08 (car l-addrs-1) r-w-x x86)))))
                             (x86-2 (mv-nth 1 (wb addr-bytes x86)))
                             (l-addrs (cdr l-addrs-1))
                             (r-w-x r-w-x)
                             (acc nil)))))))

(defun-nx rb-1-wb-subset-ind-hint
  (l-addrs-1 addr-bytes r-w-x cpl x86 acc)
  (if (endp l-addrs-1)
      acc
    (rb-1-wb-subset-ind-hint
     (cdr l-addrs-1) addr-bytes r-w-x cpl
     (mv-nth 2 (rm08 (car l-addrs-1) r-w-x x86))
     (append
      acc
      (list
       (nth
        (pos
         (mv-nth 1 (ia32e-entries-found-la-to-pa (car l-addrs-1) r-w-x cpl x86))
         (translate-all-l-addrs (strip-cars addr-bytes) :w cpl x86))
        (strip-cdrs addr-bytes)))))))

(defthmd rb-1-wb-subset-in-system-level-mode
  (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
                (all-paging-entries-found-p l-addrs-1 x86)
                (all-paging-entries-found-p (strip-cars addr-bytes) x86)
                (subset-p
                 ;; The physical addresses corresponding to l-addrs-1
                 ;; are a subset of those corresponding to (strip-cars addr-bytes).
                 (translate-all-l-addrs l-addrs-1 r-w-x cpl x86)
                 (translate-all-l-addrs (strip-cars addr-bytes) :w cpl x86))
                (no-duplicates-p
                 ;; All physical addresses being written to are unique.
                 (translate-all-l-addrs (strip-cars addr-bytes) :w cpl (double-rewrite x86)))
                (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                 ;; The write isn't being done to the page tables.
                 (strip-cars addr-bytes) :w cpl (double-rewrite x86))
                (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                 l-addrs-1 r-w-x cpl (double-rewrite x86))
                (no-page-faults-during-translation-p l-addrs-1 r-w-x cpl (double-rewrite x86))
                (no-page-faults-during-translation-p (strip-cars addr-bytes) :w cpl (double-rewrite x86))
                (addr-byte-alistp addr-bytes)
                (true-listp acc))
           (equal (mv-nth 1 (rb-1 l-addrs-1 r-w-x (mv-nth 1 (wb addr-bytes x86)) acc))
                  (append
                   acc
                   (assoc-list
                    (translate-all-l-addrs l-addrs-1 r-w-x cpl x86)
                    (create-addr-bytes-alist
                     (translate-all-l-addrs (strip-cars addr-bytes) :w cpl x86)
                     (strip-cdrs addr-bytes))))))

  :hints (("Goal"
           :induct (rb-1-wb-subset-ind-hint l-addrs-1 addr-bytes r-w-x cpl x86 acc)
           :in-theory (e/d* (rb-1
                             wb
                             rm08-wm08-equal-in-system-level-mode
                             rm08-wm08-disjoint-in-system-level-mode
                             all-paging-entries-found-p
                             no-page-faults-during-translation-p
                             mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                             subset-p
                             rb-1-wb-subset-in-system-level-mode-helper)
                            (signed-byte-p unsigned-byte-p)))))

(defthm rb-wb-subset-in-system-level-mode
  (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
                (all-paging-entries-found-p l-addrs-1 (double-rewrite x86))
                (all-paging-entries-found-p (strip-cars addr-bytes) (double-rewrite x86))
                (subset-p
                 ;; The physical addresses corresponding to l-addrs-1
                 ;; are a subset of those corresponding to (strip-cars addr-bytes).
                 (translate-all-l-addrs l-addrs-1 r-w-x cpl (double-rewrite x86))
                 (translate-all-l-addrs (strip-cars addr-bytes) :w cpl (double-rewrite x86)))
                (no-duplicates-p
                 ;; All physical addresses being written to are unique.
                 (translate-all-l-addrs (strip-cars addr-bytes) :w cpl (double-rewrite x86)))
                (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                 ;; The write isn't being done to the page tables.
                 (strip-cars addr-bytes) :w cpl (double-rewrite x86))
                (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                 l-addrs-1 r-w-x cpl (double-rewrite x86))
                (no-page-faults-during-translation-p l-addrs-1 r-w-x cpl (double-rewrite x86))
                (no-page-faults-during-translation-p (strip-cars addr-bytes) :w cpl (double-rewrite x86))
                (addr-byte-alistp addr-bytes))
           (equal (mv-nth 1 (rb l-addrs-1 r-w-x (mv-nth 1 (wb addr-bytes x86))))
                  (assoc-list
                   (translate-all-l-addrs l-addrs-1 r-w-x cpl (double-rewrite x86))
                   (create-addr-bytes-alist
                    (translate-all-l-addrs (strip-cars addr-bytes) :w cpl (double-rewrite x86))
                    (strip-cdrs addr-bytes)))))
  :hints (("Goal" :in-theory (e/d* (rb rb-1-wb-subset-in-system-level-mode)
                                   (rb-1 signed-byte-p unsigned-byte-p
                                         force (force))))))

;; ======================================================================

;; Proving wb-remove-duplicate-writes-in-system-level-mode:

(defun-nx wb-duplicate-writes-error-induct (addr-list x86)
  (if (endp addr-list)
      nil
    (if (member-p (car (car addr-list)) (strip-cars (cdr addr-list)))
        (wb-duplicate-writes-error-induct (cdr addr-list) x86)
      (wb-duplicate-writes-error-induct
       (cdr addr-list)
       (mv-nth 1 (wb (list (car addr-list)) x86))))))

(defthm wb-remove-duplicate-writes-in-system-level-mode-error
  (implies (and (syntaxp
                 (not (and (consp addr-bytes)
                           (eq (car addr-bytes)
                               'remove-duplicate-keys))))
                (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
                (all-paging-entries-found-p
                 (strip-cars addr-bytes) (double-rewrite x86))
                (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                 ;; The write isn't being done to the page tables.
                 (strip-cars addr-bytes) :w cpl (double-rewrite x86))
                (no-page-faults-during-translation-p
                 (strip-cars addr-bytes) :w cpl (double-rewrite x86))
                (addr-byte-alistp addr-bytes))
           (equal (mv-nth 0 (wb addr-bytes x86))
                  (mv-nth 0 (wb (remove-duplicate-keys addr-bytes) x86))))
  :hints (("Goal"
           :do-not '(generalize)
           :in-theory (e/d (wb
                            all-paging-entries-found-p
                            mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                            no-page-faults-during-translation-p)
                           (acl2::mv-nth-cons-meta))
           :induct (wb-duplicate-writes-error-induct addr-bytes x86))))

(local
 (defthm mv-nth-1-wm08-and-xlate-equiv-x86s-disjoint-with-shadowed-writes
   (implies (and
             (not
              (mv-nth
               0
               (ia32e-entries-found-la-to-pa
                lin-addr-1 :w (loghead 2 (xr :seg-visible 1 x86)) x86)))
             (equal
              (mv-nth
               1
               (ia32e-entries-found-la-to-pa
                lin-addr-1 :w (loghead 2 (xr :seg-visible 1 x86)) x86))
              (mv-nth
               1
               (ia32e-entries-found-la-to-pa
                lin-addr-2 :w (loghead 2 (xr :seg-visible 1 x86)) x86)))
             (pairwise-disjoint-p-aux
              (list
               (mv-nth
                1
                (ia32e-entries-found-la-to-pa
                 lin-addr-2 :w (loghead 2 (xr :seg-visible 1 x86)) x86)))
              (open-qword-paddr-list-list
               (gather-all-paging-structure-qword-addresses x86)))
             (paging-entries-found-p lin-addr-1 (double-rewrite x86))
             (paging-entries-found-p lin-addr-2 (double-rewrite x86)))
            (xlate-equiv-x86s (mv-nth 1 (wm08 lin-addr-1 val-1 (mv-nth 1 (wm08 lin-addr-2 val-2 x86))))
                              (mv-nth 1 (wm08 lin-addr-1 val-1 x86))))
   :hints (("Goal" :in-theory (e/d* (wm08) ())))))

(local
 (defthm mv-nth-1-wm08-and-xlate-equiv-x86s-disjoint-commute-writes
   (implies (and
             (not
              (equal (mv-nth
                      1
                      (ia32e-entries-found-la-to-pa
                       lin-addr-1 :w (loghead 2 (xr :seg-visible 1 x86)) x86))
                     (mv-nth
                      1
                      (ia32e-entries-found-la-to-pa
                       lin-addr-2 :w (loghead 2 (xr :seg-visible 1 x86)) x86))))
             (pairwise-disjoint-p-aux
              ;; The write is not being done to the paging structures.
              (list
               (mv-nth
                1
                (ia32e-entries-found-la-to-pa
                 lin-addr-1 :w (loghead 2 (xr :seg-visible 1 x86)) x86)))
              (open-qword-paddr-list-list
               (gather-all-paging-structure-qword-addresses x86)))
             (pairwise-disjoint-p-aux
              ;; The write is not being done to the paging structures.
              (list
               (mv-nth
                1
                (ia32e-entries-found-la-to-pa
                 lin-addr-2 :w (loghead 2 (xr :seg-visible 1 x86)) x86)))
              (open-qword-paddr-list-list
               (gather-all-paging-structure-qword-addresses x86)))
             (paging-entries-found-p lin-addr-1 (double-rewrite x86))
             (paging-entries-found-p lin-addr-2 (double-rewrite x86)))
            (xlate-equiv-x86s (mv-nth 1 (wm08 lin-addr-1 val-1 (mv-nth 1 (wm08 lin-addr-2 val-2 x86))))
                              (mv-nth 1 (wm08 lin-addr-2 val-2 (mv-nth 1 (wm08 lin-addr-1 val-1 x86))))))
   :hints (("Goal" :in-theory (e/d* (wm08 xlate-equiv-x86s) ())))))

;; (thm
;;  (implies
;;   (and
;;    (not
;;     (equal
;;      (mv-nth
;;       1
;;       (ia32e-entries-found-la-to-pa lin-addr-1
;;                                     :w (loghead 2 (xr :seg-visible 1 x86))
;;                                     x86))
;;      (mv-nth
;;       1
;;       (ia32e-entries-found-la-to-pa lin-addr-2
;;                                     :w (loghead 2 (xr :seg-visible 1 x86))
;;                                     x86))))
;;    (pairwise-disjoint-p-aux
;;     (list
;;      (mv-nth
;;       1
;;       (ia32e-entries-found-la-to-pa lin-addr-1
;;                                     :w (loghead 2 (xr :seg-visible 1 x86))
;;                                     x86)))
;;     (open-qword-paddr-list-list
;;      (gather-all-paging-structure-qword-addresses x86)))
;;    (pairwise-disjoint-p-aux
;;     (list
;;      (mv-nth
;;       1
;;       (ia32e-entries-found-la-to-pa lin-addr-2
;;                                     :w (loghead 2 (xr :seg-visible 1 x86))
;;                                     x86)))
;;     (open-qword-paddr-list-list
;;      (gather-all-paging-structure-qword-addresses x86)))
;;    (paging-entries-found-p lin-addr-1 (double-rewrite x86))
;;    (paging-entries-found-p lin-addr-2 (double-rewrite x86)))
;;   (xlate-equiv-x86s (mv-nth 1
;;                             (wm08 lin-addr-1 val-1
;;                                   (mv-nth 1 (wm08 lin-addr-2 val-2
;;                                                   (mv-nth 1 (wm08 lin-addr-1 val-old x86))))))
;;                     (mv-nth 1 (wm08 lin-addr-1 val-1
;;                                     (mv-nth 1 (wm08 lin-addr-2 val-2 x86))))))
;;  :hints (("Goal" :in-theory (e/d* (wm08) ()))))


(define wb-shadows-wm08-ind-hint
  ((cpl :type (unsigned-byte 2))
   (lin-addr :type (signed-byte 48))
   (addr-bytes (addr-byte-alistp addr-bytes))
   x86)

  :non-executable t
  :enabled t

  (if (endp addr-bytes)
      x86

    (if (equal
         (mv-nth 1 (ia32e-entries-found-la-to-pa lin-addr :w cpl x86))
         (mv-nth 1 (ia32e-entries-found-la-to-pa (car (car addr-bytes)) :w cpl x86)))

        x86

      (wb-shadows-wm08-ind-hint
       cpl lin-addr (cdr addr-bytes)
       (mv-nth 1 (wm08 (car (car addr-bytes)) (cdr (car addr-bytes)) x86))))))

(local
 (defthm wb-shadows-wm08-helper
   ;; Follows from:
   ;; mv-nth-1-wm08-and-xlate-equiv-structures-disjoint
   ;; mv-nth-1-ia32e-entries-found-la-to-pa-with-xlate-equiv-structures
   (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
                 (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                  (strip-cars addr-bytes) :w cpl (double-rewrite x86))
                 (all-paging-entries-found-p (strip-cars addr-bytes) (double-rewrite x86))
                 (consp addr-bytes))
            (equal (mv-nth 1
                           (ia32e-entries-found-la-to-pa
                            lin-addr :w
                            cpl
                            (mv-nth 1
                                    (wm08 (car (car addr-bytes))
                                          (cdr (car addr-bytes))
                                          x86))))
                   (mv-nth 1
                           (ia32e-entries-found-la-to-pa
                            lin-addr :w
                            cpl
                            x86))))
   :hints (("Goal"
            :do-not-induct t
            :in-theory (e/d* (all-paging-entries-found-p
                              no-page-faults-during-translation-p
                              mapped-lin-addrs-disjoint-from-paging-structure-addrs-p)
                             ())))))

(local
 (defthm gather-all-paging-structure-qword-addresses-wm08-disjoint
   (implies
    (and
     (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
     (equal addrs (gather-all-paging-structure-qword-addresses x86))
     (pairwise-disjoint-p-aux
      (list (mv-nth 1 (ia32e-entries-found-la-to-pa lin-addr :w cpl x86)))
      (open-qword-paddr-list-list addrs))
     (paging-entries-found-p lin-addr (double-rewrite x86)))
    (equal (gather-all-paging-structure-qword-addresses (mv-nth 1 (wm08 lin-addr val x86)))
           addrs))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d* (wm08) ())))))

(local
 (defthm wb-shadows-wm08
   (implies (and
             (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
             (member-p
              (mv-nth 1 (ia32e-entries-found-la-to-pa lin-addr :w cpl x86))
              (translate-all-l-addrs (strip-cars addr-bytes) :w cpl x86))
             (pairwise-disjoint-p-aux
              (list (mv-nth 1 (ia32e-entries-found-la-to-pa lin-addr :w cpl x86)))
              (open-qword-paddr-list-list (gather-all-paging-structure-qword-addresses x86)))
             (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
              (strip-cars addr-bytes) :w cpl (double-rewrite x86))
             (all-paging-entries-found-p (strip-cars addr-bytes) (double-rewrite x86))
             (paging-entries-found-p lin-addr (double-rewrite x86))
             (no-page-faults-during-translation-p (strip-cars addr-bytes) :w cpl x86)
             (not (mv-nth 0 (ia32e-entries-found-la-to-pa lin-addr :w cpl x86)))
             (addr-byte-alistp addr-bytes))
            (xlate-equiv-x86s (mv-nth 1 (wb addr-bytes (mv-nth 1 (wm08 lin-addr val x86))))
                              (mv-nth 1 (wb addr-bytes x86))))
   :hints (("Goal"
            :induct (wb-shadows-wm08-ind-hint cpl lin-addr addr-bytes x86)
            :in-theory (e/d* (wb
                              mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                              no-page-faults-during-translation-p
                              all-paging-entries-found-p)
                             (mv-nth-1-wm08-and-xlate-equiv-x86s-disjoint-commute-writes)))
           ("Subgoal *1/3"
            :expand (wb addr-bytes (mv-nth 1 (wm08 lin-addr val x86)))
            :in-theory (e/d* (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                              no-page-faults-during-translation-p
                              all-paging-entries-found-p)
                             ()))
           ("Subgoal *1/3.7"
            :expand (wb addr-bytes x86)
            :use ((:instance mv-nth-1-wm08-and-xlate-equiv-x86s-disjoint-commute-writes
                             (lin-addr-1 (car (car addr-bytes)))
                             (val-1 (cdr (car addr-bytes)))
                             (lin-addr-2 lin-addr)
                             (val-2 val)
                             (x86 x86))
                  (:instance mv-nth-1-wb-and-xlate-equiv-x86s-disjoint
                             (addr-bytes (cdr addr-bytes))
                             (x86-1 (mv-nth 1
                                            (wm08 lin-addr
                                                  val
                                                  (mv-nth
                                                   1
                                                   (wm08
                                                    (car (car addr-bytes))
                                                    (cdr (car addr-bytes))
                                                    x86)))))
                             (x86-2 (mv-nth 1
                                            (wm08 (car (car addr-bytes))
                                                  (cdr (car addr-bytes))
                                                  (mv-nth 1 (wm08 lin-addr val x86)))))))
            :in-theory (e/d* (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                              no-page-faults-during-translation-p
                              all-paging-entries-found-p)
                             (mv-nth-1-wm08-and-xlate-equiv-x86s-disjoint-commute-writes
                              mv-nth-1-wb-and-xlate-equiv-x86s-disjoint)))
           ("Subgoal *1/2"
            :expand (wb addr-bytes (mv-nth 1 (wm08 lin-addr val x86)))
            :in-theory (e/d* (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                              no-page-faults-during-translation-p
                              all-paging-entries-found-p)
                             ()))
           ("Subgoal *1/2.1"
            :expand (wb addr-bytes x86)
            :in-theory (e/d* (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                              no-page-faults-during-translation-p
                              all-paging-entries-found-p)
                             ())
            :use ((:instance mv-nth-1-wb-and-xlate-equiv-x86s-disjoint
                             (addr-bytes (cdr addr-bytes))
                             (x86-1 (mv-nth 1
                                            (wm08 (car (car addr-bytes))
                                                  (cdr (car addr-bytes))
                                                  (mv-nth 1 (wm08 lin-addr val x86)))))
                             (x86-2 (mv-nth 1
                                            (wm08 (car (car addr-bytes))
                                                  (cdr (car addr-bytes))
                                                  x86)))))))))

(define remove-shadowed-writes-to-physical-addresses
  ((cpl :type (unsigned-byte 2))
   (addr-bytes (addr-byte-alistp addr-bytes))
   x86)
  ;; TO-DO: Make this function executable.
  :non-executable t
  :enabled t
  (if (endp addr-bytes)
      nil
    (if
        ;; If the physical address corresponding to (car (car
        ;; addr-bytes)) is also present in (strip-cars (cdr
        ;; addr-bytes)), then (car (car addr-bytes)) is stale.
        (member-p
         (mv-nth 1 (ia32e-entries-found-la-to-pa (car (car addr-bytes)) :w cpl x86))
         (translate-all-l-addrs (strip-cars (cdr addr-bytes)) :w cpl x86))

        (remove-shadowed-writes-to-physical-addresses cpl (cdr addr-bytes) x86)

      (cons (car addr-bytes)
            (remove-shadowed-writes-to-physical-addresses cpl (cdr addr-bytes) x86))))

  ///

  (defthm addr-byte-alistp-of-remove-shadowed-writes-to-physical-addresses
    (implies (addr-byte-alistp as)
             (addr-byte-alistp (remove-shadowed-writes-to-physical-addresses cpl as x86))))

  (defthm remove-shadowed-writes-to-physical-addresses-and-xlate-equiv-structures
    (implies (xlate-equiv-structures x86-1 x86-2)
             (equal (remove-shadowed-writes-to-physical-addresses cpl addr-bytes x86-1)
                    (remove-shadowed-writes-to-physical-addresses cpl addr-bytes x86-2)))
    :rule-classes :congruence)

  (defthm remove-shadowed-writes-to-physical-addresses-and-xlate-equiv-x86s
    (implies (xlate-equiv-x86s x86-1 x86-2)
             (equal (remove-shadowed-writes-to-physical-addresses cpl addr-bytes x86-1)
                    (remove-shadowed-writes-to-physical-addresses cpl addr-bytes x86-2)))
    :rule-classes :congruence))

(define wb-remove-shadowed-writes-ind-hint
  ((cpl :type (unsigned-byte 2))
   (addr-bytes (addr-byte-alistp addr-bytes))
   x86)
  :non-executable t
  :enabled t
  (if (endp addr-bytes)
      x86
    (if
        ;; If the physical address corresponding to (car (car
        ;; addr-bytes)) is also present in (strip-cars (cdr
        ;; addr-bytes)), then the write to (car (car addr-bytes)) is
        ;; stale.
        (member-p
         (mv-nth 1 (ia32e-entries-found-la-to-pa (car (car addr-bytes)) :w cpl x86))
         (translate-all-l-addrs (strip-cars (cdr addr-bytes)) :w cpl x86))

        (wb-remove-shadowed-writes-ind-hint
         cpl (cdr addr-bytes) x86)

      (wb-remove-shadowed-writes-ind-hint
       cpl (cdr addr-bytes)
       (mv-nth 1 (wm08 (car (car addr-bytes)) (cdr (car addr-bytes)) x86))))))


(defthmd wb-remove-duplicate-writes-in-system-level-mode
  (implies (and (syntaxp
                 (not (and (consp addr-bytes)
                           (eq (car addr-bytes)
                               'remove-shadowed-writes-to-physical-addresses))))
                (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
                (all-paging-entries-found-p
                 (strip-cars addr-bytes) (double-rewrite x86))
                (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                 ;; The write isn't being done to the page tables.
                 (strip-cars addr-bytes) :w cpl (double-rewrite x86))
                (no-page-faults-during-translation-p
                 (strip-cars addr-bytes) :w cpl (double-rewrite x86))
                (addr-byte-alistp addr-bytes))
           (xlate-equiv-x86s (mv-nth 1 (wb addr-bytes x86))
                             (mv-nth 1 (wb (remove-shadowed-writes-to-physical-addresses
                                            cpl addr-bytes x86)
                                           x86))))
  :hints (("Goal"
           :induct (wb-remove-shadowed-writes-ind-hint cpl addr-bytes x86)
           :do-not '(generalize)
           :expand (wb addr-bytes x86)
           :in-theory (e/d (wb
                            all-paging-entries-found-p
                            mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                            no-page-faults-during-translation-p)
                           (acl2::mv-nth-cons-meta)))))

;; ======================================================================

;; Proofs of rb-in-terms-of-nth-and-pos-in-system-level-mode,
;; rb-in-terms-of-rb-subset-p-in-system-level-mode, and
;; combine-bytes-rb-in-terms-of-rb-subset-p-in-system-level-mode:

(defthmd car-of-rb
  (implies (canonical-address-listp l-addrs)
           (equal (car (mv-nth 1 (rb l-addrs r-w-x x86)))
                  (car (mv-nth 1 (rb (list (car l-addrs)) r-w-x x86)))))
  :hints (("Goal" :in-theory (e/d* (rb) ()))))

(local
 (defthm rb-in-terms-of-nth-and-pos-in-system-level-mode-helper
   (implies (and (syntaxp
                  (and (consp anything)
                       (eq (car anything)
                           'create-canonical-address-list)))
                 (canonical-address-listp anything)
                 (signed-byte-p 48 addr))
            (equal (car (mv-nth 1 (rb (cons addr anything) r-w-x x86)))
                   (car (mv-nth 1 (rb (list addr) r-w-x x86)))))
   :hints (("Goal" :use ((:instance car-of-rb
                                    (l-addrs (cons addr anything))))))))

(defthm consp-rb
  (implies (and (consp l-addrs)
                (no-page-faults-during-translation-p
                 l-addrs r-w-x (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)) (double-rewrite x86))
                (all-paging-entries-found-p l-addrs (double-rewrite x86)))
           (consp (mv-nth 1 (rb l-addrs r-w-x x86))))
  :hints (("Goal" :in-theory (e/d* (rb
                                    all-paging-entries-found-p
                                    no-page-faults-during-translation-p)
                                   ())))
  :rule-classes (:type-prescription :rewrite))

(defthmd paging-entry-found-p-and-integerp-lin-addr
  (implies (and (bind-free (find-binding-from-entry-found-p 'x86 mfc state) (x86))
                (paging-entries-found-p lin-addr x86))
           (integerp lin-addr))
  :hints (("Goal" :use ((:instance entry-found-p-and-lin-addr)))))

(defun find-info-from-program-at-term (thm mfc state)
  ;; From programmer-level-memory-utils.
  (declare (xargs :stobjs (state) :mode :program)
           (ignorable thm state))
  (b* ((call (acl2::find-call-lst 'program-at (acl2::mfc-clause mfc)))
       ((when (not call))
        ;; (cw "~%~p0: Program-At term not encountered.~%" thm)
        nil)
       (addresses (cadr call))
       ((when (not (equal (car addresses)
                          'create-canonical-address-list)))
        ;; (cw "~%~p0: Program-At without Create-Canonical-Address-List encountered.~%" thm)
        nil)
       (n (cadr addresses))
       (prog-addr (caddr addresses))
       (bytes (caddr call)))
    `((n . ,n)
      (prog-addr . ,prog-addr)
      (bytes . ,bytes))))

(defthm rb-in-terms-of-nth-and-pos-in-system-level-mode
  (implies (and
            (bind-free (find-info-from-program-at-term
                        'rb-in-terms-of-nth-and-pos-in-system-level-mode
                        mfc state)
                       (n prog-addr bytes))
            (program-at (create-canonical-address-list n prog-addr)
                        bytes x86)
            (member-p addr (create-canonical-address-list n prog-addr))
            (syntaxp (quotep n))
            (canonical-address-p prog-addr)
            (all-paging-entries-found-p
             (create-canonical-address-list n prog-addr) (double-rewrite x86))
            (no-page-faults-during-translation-p
             (create-canonical-address-list n prog-addr) :x
             (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)) (double-rewrite x86))
            (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
             (create-canonical-address-list n prog-addr) :x
             (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)) (double-rewrite x86)))
           (equal (car (mv-nth 1 (rb (list addr) :x x86)))
                  (nth (pos addr (create-canonical-address-list n prog-addr)) bytes)))
  :hints (("Goal"
           :in-theory (e/d* (program-at
                             paging-entry-found-p-and-integerp-lin-addr
                             no-page-faults-during-translation-p
                             all-paging-entries-found-p
                             mapped-lin-addrs-disjoint-from-paging-structure-addrs-p)
                            (acl2::mv-nth-cons-meta
                             member-p-canonical-address-p-canonical-address-listp
                             rb)))
          ("Subgoal *1/7"
           :expand (rb (cons prog-addr
                             (create-canonical-address-list
                              (+ -1 n) (+ 1 prog-addr)))
                       :x x86)
           :in-theory (e/d* (program-at
                             paging-entry-found-p-and-integerp-lin-addr
                             rb
                             no-page-faults-during-translation-p
                             all-paging-entries-found-p
                             mapped-lin-addrs-disjoint-from-paging-structure-addrs-p)
                            (acl2::mv-nth-cons-meta
                             member-p-canonical-address-p-canonical-address-listp)))))

(defthmd rb-unwinding-thm-in-system-level-mode
  (implies
   (and
    (consp l-addrs)
    (all-paging-entries-found-p l-addrs (double-rewrite x86))
    (no-page-faults-during-translation-p
     l-addrs r-w-x (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86))
     (double-rewrite x86))
    (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
     l-addrs r-w-x
     (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86))
     (double-rewrite x86)))
   (equal (mv-nth 1 (rb l-addrs r-w-x x86))
          (cons (car (mv-nth 1 (rb (list (car l-addrs)) r-w-x x86)))
                (mv-nth 1 (rb (cdr l-addrs) r-w-x x86)))))
  :hints (("Goal" :in-theory (e/d* (rb
                                    all-paging-entries-found-p
                                    mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                                    no-page-faults-during-translation-p)
                                   ()))))

(defthm rb-in-terms-of-rb-subset-p-in-system-level-mode
  (implies
   (and
    (bind-free (find-info-from-program-at-term
                'rb-in-terms-of-rb-subset-p-in-system-level-mode
                mfc state)
               (n prog-addr bytes))
    (program-at (create-canonical-address-list n prog-addr) bytes x86)
    (subset-p addresses (create-canonical-address-list n prog-addr))
    (consp addresses)
    (all-paging-entries-found-p
     (create-canonical-address-list n prog-addr) (double-rewrite x86))
    (no-page-faults-during-translation-p
     (create-canonical-address-list n prog-addr)
     :x (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)) (double-rewrite x86))
    (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
     (create-canonical-address-list n prog-addr)
     :x (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)) (double-rewrite x86))
    (syntaxp (quotep n)))
   (equal (mv-nth 1 (rb addresses :x x86))
          (append (list (nth (pos
                              (car addresses)
                              (create-canonical-address-list n prog-addr))
                             bytes))
                  (mv-nth 1 (rb (cdr addresses) :x x86)))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (subset-p)
                           (canonical-address-p
                            acl2::mv-nth-cons-meta
                            rb-in-terms-of-nth-and-pos-in-system-level-mode))
           :use ((:instance rb-in-terms-of-nth-and-pos-in-system-level-mode
                            (addr (car addresses)))
                 (:instance rb-unwinding-thm-in-system-level-mode
                            (l-addrs addresses)
                            (r-w-x :x))))))

(defthm combine-bytes-rb-in-terms-of-rb-subset-p-in-system-level-mode
  (implies
   (and
    (bind-free (find-info-from-program-at-term
                'combine-bytes-rb-in-terms-of-rb-subset-p-in-system-level-mode
                mfc state)
               (n prog-addr bytes))
    (program-at (create-canonical-address-list n prog-addr) bytes x86)
    (subset-p addresses (create-canonical-address-list n prog-addr))
    (consp addresses)
    (all-paging-entries-found-p
     (create-canonical-address-list n prog-addr) (double-rewrite x86))
    (no-page-faults-during-translation-p
     (create-canonical-address-list n prog-addr)
     :x (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)) (double-rewrite x86))
    (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
     (create-canonical-address-list n prog-addr)
     :x (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)) (double-rewrite x86))
    (syntaxp (quotep n)))
   (equal
    (combine-bytes (mv-nth 1 (rb addresses :x x86)))
    (combine-bytes
     (append (list (nth (pos (car addresses)
                             (create-canonical-address-list n prog-addr))
                        bytes))
             (mv-nth 1 (rb (cdr addresses) :x x86))))))
  :hints (("Goal" :in-theory (union-theories
                              '()
                              (theory 'minimal-theory))
           :use ((:instance rb-in-terms-of-rb-subset-p-in-system-level-mode)))))

;; ======================================================================

;; Some other RoWs required in the system-level mode:

(defthm rb-pop-x86-oracle-in-system-level-mode
  (implies (case-split (not (programmer-level-mode x86)))
           (and
            (equal (mv-nth 0 (rb addresses r-w-x (mv-nth 1 (pop-x86-oracle x86))))
                   (mv-nth 0 (rb addresses r-w-x x86)))
            (equal (mv-nth 1 (rb addresses r-w-x (mv-nth 1 (pop-x86-oracle x86))))
                   (mv-nth 1 (rb addresses r-w-x x86)))))
  :hints (("Goal" :in-theory (e/d (pop-x86-oracle pop-x86-oracle-logic)
                                  (rb)))))

(defthm rb-!flgi-in-system-level-mode
  (implies (case-split (not (programmer-level-mode x86)))
           (and
            (equal (mv-nth 0 (rb addresses r-w-x (!flgi flg val x86)))
                   (mv-nth 0 (rb addresses r-w-x x86)))
            (equal (mv-nth 1 (rb addresses r-w-x (!flgi flg val x86)))
                   (mv-nth 1 (rb addresses r-w-x x86)))))
  :hints (("Goal" :in-theory (e/d (!flgi)
                                  (force (force))))))

(defthm rb-!flgi-undefined-in-system-level-mode
  (implies (case-split (not (programmer-level-mode x86)))
           (and
            (equal (mv-nth 0 (rb addresses r-w-x (!flgi-undefined flg x86)))
                   (mv-nth 0 (rb addresses r-w-x x86)))
            (equal (mv-nth 1 (rb addresses r-w-x (!flgi-undefined flg x86)))
                   (mv-nth 1 (rb addresses r-w-x x86)))))
  :hints (("Goal" :in-theory (e/d (!flgi-undefined)
                                  (force (force))))))

(defthm flgi-and-rb-in-system-level-mode
  (implies (case-split (not (programmer-level-mode x86)))
           (equal (flgi i (mv-nth 2 (rb l-addrs r-w-x x86)))
                  (flgi i x86)))
  :hints (("Goal" :in-theory (e/d* (flgi)
                                   (force (force))))))

(defthm alignment-checking-enabled-p-and-rb-in-system-level-mode
  (implies (case-split (not (programmer-level-mode x86)))
           (equal (alignment-checking-enabled-p (mv-nth 2 (rb l-addrs r-w-x x86)))
                  (alignment-checking-enabled-p x86)))
  :hints (("Goal" :in-theory (e/d* (alignment-checking-enabled-p)
                                   (force (force))))))

(defthm flgi-wb-in-system-level-mode
  (implies (case-split (not (programmer-level-mode x86)))
           (equal (flgi flg (mv-nth 1 (wb addr-bytes-alst x86)))
                  (flgi flg x86)))
  :hints (("Goal" :in-theory (e/d* (flgi) (force (force))))))

(defthm alignment-checking-enabled-p-and-wb-in-system-level-mode
  (implies (not (programmer-level-mode x86))
           (equal (alignment-checking-enabled-p (mv-nth 1 (wb addr-bytes-alst x86)))
                  (alignment-checking-enabled-p x86)))
  :hints (("Goal" :in-theory (e/d* (alignment-checking-enabled-p)
                                   (force (force))))))

;; ======================================================================

#||

We need the following kind of lemmas in this book to make it similar
in functionality to programmer-level-memory-utils.

(defthm rb-wb-disjoint
  (implies (and (disjoint-p addresses (strip-cars addr-lst))
                (programmer-level-mode x86))
           (equal (mv-nth 1 (rb addresses r-w-x (mv-nth 1 (wb addr-lst x86))))
                  (mv-nth 1 (rb addresses r-w-x x86))))
  :hints (("Goal" :in-theory (e/d (disjoint-p) ()))))

(defthmd rb-wb-equal
  (implies (and (equal addresses (strip-cars (remove-duplicate-keys addr-lst)))
                (programmer-level-mode x86)
                (addr-byte-alistp addr-lst))
           (equal (mv-nth 1 (rb addresses r-w-x (mv-nth 1 (wb addr-lst x86))))
                  (assoc-list addresses (reverse addr-lst))))
  :hints (("Goal" :in-theory (e/d (wm08 rm08) ()))))

(defthm rb-wb-subset
  (implies (and (subset-p addresses (strip-cars addr-lst))
                (programmer-level-mode x86)
                ;; [Shilpi]: Ugh, this hyp. below is so annoying. I
                ;; could remove it if I proved something like
                ;; subset-p-strip-cars-of-remove-duplicate-keys,
                ;; commented out below.
                (canonical-address-listp addresses)
                (addr-byte-alistp addr-lst))
           (equal (mv-nth 1 (rb addresses r-w-x (mv-nth 1 (wb addr-lst x86))))
                  (assoc-list addresses (reverse addr-lst))))
  :hints (("Goal" :induct (assoc-list addresses (reverse addr-lst)))))

(defthmd rb-rb-subset
  ;; [Shilpi]: This theorem can be generalized so that the conclusion mentions
  ;; addr1, where addr1 <= addr.  Also, this is an expensive rule. Keep it
  ;; disabled generally.
  (implies (and (equal (mv-nth 1 (rb (create-canonical-address-list i addr) r-w-x x86))
                       bytes)
                (canonical-address-p (+ -1 i addr))
                (canonical-address-p addr)
                (xr :programmer-level-mode 0 x86)
                (posp i)
                (< j i))
           (equal (mv-nth 1 (rb (create-canonical-address-list j addr) r-w-x x86))
                  (take j bytes)))
  :hints (("Goal" :in-theory (e/d* (rb canonical-address-p signed-byte-p) ()))))

(defthm rb-rb-split-reads
  (implies (and (canonical-address-p addr)
                (xr :programmer-level-mode 0 x86)
                (natp j)
                (natp k))
           (equal (mv-nth 1 (rb (create-canonical-address-list (+ k j) addr) r-w-x x86))
                  (append (mv-nth 1 (rb (create-canonical-address-list k addr) r-w-x x86))
                          (mv-nth 1 (rb (create-canonical-address-list j (+ k addr)) r-w-x x86)))))
  :hints (("Goal" :in-theory (e/d* (rb canonical-address-p signed-byte-p)
                                   ((:meta acl2::mv-nth-cons-meta))))))

(defthm program-at-wb-disjoint
  (implies (and (programmer-level-mode x86)
                (canonical-address-listp addresses)
                (disjoint-p addresses (strip-cars addr-lst)))
           (equal (program-at addresses r-w-x (mv-nth 1 (wb addr-lst x86)))
                  (program-at addresses r-w-x x86)))
  :hints (("Goal" :in-theory (e/d (program-at) (rb)))))

(defthm program-at-pop-x86-oracle
  (implies (programmer-level-mode x86)
           (equal (program-at addresses r-w-x (mv-nth 1 (pop-x86-oracle x86)))
                  (program-at addresses r-w-x x86)))
  :hints (("Goal" :in-theory (e/d (program-at pop-x86-oracle pop-x86-oracle-logic)
                                  (rb)))))

(defthm program-at-write-user-rflags
  (implies (programmer-level-mode x86)
           (equal (program-at addresses r-w-x (write-user-rflags flags mask x86))
                  (program-at addresses r-w-x x86)))
  :hints (("Goal" :in-theory (e/d (write-user-rflags)
                                  (force (force))))))


(defthm wb-and-wb-combine-wbs
  (implies (and (addr-byte-alistp addr-list1)
                (addr-byte-alistp addr-list2)
                (programmer-level-mode x86))
           (equal (mv-nth 1 (wb addr-list2 (mv-nth 1 (wb addr-list1 x86))))
                  (mv-nth 1 (wb (append addr-list1 addr-list2) x86))))
  :hints (("Goal" :do-not '(generalize)
           :in-theory (e/d (wb-and-wm08) (append acl2::mv-nth-cons-meta)))))

(defthmd wb-remove-duplicate-writes
  (implies (and (syntaxp
                 (not
                  (and (consp addr-list)
                       (eq (car addr-list) 'remove-duplicate-keys))))
                (addr-byte-alistp addr-list)
                (programmer-level-mode x86))
           (equal (wb addr-list x86)
                  (wb (remove-duplicate-keys addr-list) x86)))
  :hints (("Goal" :do-not '(generalize)
           :in-theory (e/d (wm08)
                           (acl2::mv-nth-cons-meta))
           :induct (wb-duplicate-writes-induct addr-list x86))))

(defthm rb-in-terms-of-nth-and-pos
  (implies (and (bind-free (find-info-from-program-at-term
                            'rb-in-terms-of-nth-and-pos
                            mfc state)
                           (n prog-addr bytes))
                (program-at (create-canonical-address-list n prog-addr) bytes x86)
                (member-p addr (create-canonical-address-list n prog-addr))
                (syntaxp (quotep n))
                (programmer-level-mode x86))
           (equal (car (mv-nth 1 (rb (list addr) :x x86)))
                  (nth (pos addr (create-canonical-address-list n prog-addr)) bytes)))
  :hints (("Goal" :in-theory (e/d (program-at)
                                  (acl2::mv-nth-cons-meta
                                   rm08-in-terms-of-rb
                                   member-p-canonical-address-p-canonical-address-listp
                                   rb))
           :use ((:instance rm08-in-terms-of-rb
                            (r-w-x :x))
                 (:instance member-p-canonical-address-p-canonical-address-listp
                            (e addr))
                 (:instance rm08-in-terms-of-nth-pos-and-rb
                            (r-w-x :x)
                            (addresses (create-canonical-address-list n prog-addr)))))))

(defthm rb-in-terms-of-rb-subset-p
  (implies
   (and (bind-free (find-info-from-program-at-term
                    'rb-in-terms-of-rb-subset-p
                    mfc state)
                   (n prog-addr bytes))
        (program-at (create-canonical-address-list n prog-addr) bytes x86)
        (subset-p addresses (create-canonical-address-list n prog-addr))
        (consp addresses)
        (syntaxp (quotep n))
        (programmer-level-mode x86))
   (equal (mv-nth 1 (rb addresses :x x86))
          (append (list (nth (pos
                              (car addresses)
                              (create-canonical-address-list n prog-addr))
                             bytes))
                  (mv-nth 1 (rb (cdr addresses) :x x86)))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (subset-p)
                           (canonical-address-p
                            acl2::mv-nth-cons-meta
                            rb-in-terms-of-nth-and-pos))
           :use ((:instance rb-unwinding-thm
                            (r-w-x :x))
                 (:instance rb-in-terms-of-nth-and-pos
                            (addr (car addresses)))))))

(defthm combine-bytes-rb-in-terms-of-rb-subset-p
  (implies
   (and (bind-free (find-info-from-program-at-term
                    'combine-bytes-rb-in-terms-of-rb-subset-p
                    mfc state)
                   (n prog-addr bytes))
        (program-at (create-canonical-address-list n prog-addr) bytes x86)
        (subset-p addresses (create-canonical-address-list n prog-addr))
        (consp addresses)
        (syntaxp (quotep n))
        (programmer-level-mode x86))
   (equal
    (combine-bytes (mv-nth 1 (rb addresses :x x86)))
    (combine-bytes
     (append (list (nth (pos (car addresses)
                             (create-canonical-address-list n prog-addr))
                        bytes))
             (mv-nth 1 (rb (cdr addresses) :x x86))))))
  :hints (("Goal" :in-theory (union-theories
                              '()
                              (theory 'minimal-theory))
           :use ((:instance rb-in-terms-of-rb-subset-p)))))

(globally-disable '(rb wb canonical-address-p program-at
                       unsigned-byte-p signed-byte-p))

||#
