;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")
(include-book "paging-lib/paging-top")

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "std/lists/nthcdr" :dir :system))
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
   [mv-nth-0-wm08-and-xlate-equiv-structures]

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

1. Equality of error of wb from two xlate-equiv-structures
   [mv-nth-0-wb-and-xlate-equiv-structures]

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

(defthm true-listp-create-addr-bytes-alist
  (true-listp (create-addr-bytes-alist l-addrs bytes))
  :rule-classes :type-prescription)

(defthm create-addr-bytes-alist-bytes=nil
  (equal (create-addr-bytes-alist l-addrs nil) nil))

(defthm create-addr-bytes-alist-l-addrs=nil
  (equal (create-addr-bytes-alist nil bytes) nil))

(defthm cdr-of-create-addr-bytes-alist
  (equal (cdr (create-addr-bytes-alist l-addrs bytes))
         (create-addr-bytes-alist (cdr l-addrs) (cdr bytes))))

(defthm caar-of-create-addr-bytes-alist
  (implies (equal (len l-addrs) (len bytes))
           (equal (car (car (create-addr-bytes-alist l-addrs bytes)))
                  (car l-addrs))))

(defthm cdar-of-create-addr-bytes-alist
  (implies (equal (len l-addrs) (len bytes))
           (equal (cdr (car (create-addr-bytes-alist l-addrs bytes)))
                  (car bytes))))

(local
 (defthm nth-pos-1-and-cdr
   (implies (and (not (equal e (car x)))
                 (member-p e x)
                 (natp n))
            (equal (nth (pos-1 e x n) y)
                   (nth (pos-1 e (cdr x) n) (cdr y))))))

(defthm nth-pos-and-cdr
  (implies (and (not (equal e (car x)))
                (member-p e x))
           (equal (nth (pos e x) y)
                  (nth (pos e (cdr x)) (cdr y))))
  :hints (("Goal" :in-theory (e/d* (pos) ()))))

(local
 (defthm nth-pos-1-and-cdr-and-minus
   (implies (and (not (equal e (car x)))
                 (member-p e x)
                 (natp n))
            (equal (nth (- (pos-1 e x n) n) y)
                   (nth (- (pos-1 e (cdr x) n) n) (cdr y))))))

(local
 (defthm assoc-equal-and-nth-pos-1
   (implies (and (equal (len l-addrs) (len bytes))
                 (member-p e l-addrs)
                 (natp n))
            (equal (cdr (assoc-equal e (create-addr-bytes-alist l-addrs bytes)))
                   (nth (- (pos-1 e l-addrs n) n) bytes)))
   :hints (("Goal"
            :induct (create-addr-bytes-alist l-addrs bytes)
            :in-theory (e/d* () (nth-pos-1-and-cdr-and-minus)))
           ("Subgoal *1/2"
            :in-theory (e/d* () (nth-pos-1-and-cdr-and-minus))
            :use ((:instance nth-pos-1-and-cdr-and-minus
                             (e e)
                             (x l-addrs)
                             (y bytes)
                             (n n)))))))

(defthm assoc-equal-and-nth-pos
  (implies (and (equal (len l-addrs) (len bytes))
                (member-p e l-addrs))
           (equal (cdr (assoc-equal e (create-addr-bytes-alist l-addrs bytes)))
                  (nth (pos e l-addrs) bytes)))
  :hints (("Goal" :in-theory (e/d* (pos) (assoc-equal-and-nth-pos-1))
           :use ((:instance assoc-equal-and-nth-pos-1
                            (n 0))))))

(defthm len-of-strip-cdrs
  (equal (len (strip-cdrs as)) (len as)))

(defthm len-of-strip-cars
  (equal (len (strip-cars as)) (len as)))

(defthm wb-nil-lemma
  (equal (mv-nth 1 (wb nil x86))
         x86)
  :hints (("Goal" :in-theory (e/d* (wb) ()))))

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

(DEFTHM STRIP-CARS-OF-CREATE-ADDR-BYTES-ALIST-new
  (IMPLIES (AND (true-listp addrs)
                (EQUAL (LEN ADDRS) (LEN BYTES)))
           (EQUAL (STRIP-CARS (CREATE-ADDR-BYTES-ALIST ADDRS BYTES))
                  ADDRS)))

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

(defthmd rb-rb-split-reads-in-system-level-mode
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

(defthmd mv-nth-2-rb-1-and-accumulator
  (equal (mv-nth 2 (rb-1 l-addrs r-w-x x86 acc-1))
         (mv-nth 2 (rb-1 l-addrs r-w-x x86 acc-2))))

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

;; Relating top-level memory accessors and updaters with rb and wb in
;; system-level mode:

(defthmd rm08-to-rb-in-system-level-mode
  (implies (force (paging-entries-found-p lin-addr (double-rewrite x86)))
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

(defthmd wm08-to-wb-in-system-level-mode
  (implies (forced-and (paging-entries-found-p lin-addr (double-rewrite x86))
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

;; (i-am-here)

;; ;; ----------------------------------------------------------------------

;; (defthmd rm16-to-rb-in-system-level-mode
;;   (implies
;;    (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
;;         (equal l-addrs (create-canonical-address-list 2 lin-addr))
;;         (equal (len l-addrs) 2)
;;         (all-paging-entries-found-p l-addrs (double-rewrite x86))
;;         (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p l-addrs r-w-x cpl (double-rewrite x86))
;;         (no-page-faults-during-translation-p l-addrs r-w-x cpl (double-rewrite x86)))
;;    (equal (rm16 lin-addr r-w-x x86)
;;           (b* (((mv flg bytes x86)
;;                 (rb l-addrs r-w-x x86))
;;                (result (combine-bytes bytes)))
;;             (mv flg result x86))))
;;   :hints (("Goal"
;;            :in-theory (e/d* (all-paging-entries-found-p
;;                              mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
;;                              no-page-faults-during-translation-p
;;                              rm16
;;                              rm08
;;                              rb)
;;                             (cons-equal
;;                              signed-byte-p
;;                              unsigned-byte-p
;;                              bitops::logior-equal-0
;;                              rm08-to-rb-in-system-level-mode
;;                              (:meta acl2::mv-nth-cons-meta)
;;                              mv-nth-1-rb-1-and-xlate-equiv-x86s-disjoint
;;                              force (force))))))

;; (defthmd wm16-to-wb-in-system-level-mode
;;   (implies
;;    (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
;;         (equal l-addrs (create-canonical-address-list 2 lin-addr))
;;         (equal (len l-addrs) 2)
;;         (all-paging-entries-found-p l-addrs (double-rewrite x86))
;;         (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p l-addrs :w cpl (double-rewrite x86))
;;         (no-page-faults-during-translation-p l-addrs :w cpl (double-rewrite x86)))
;;    (equal (wm16 lin-addr word x86)
;;           (b* (((mv flg x86)
;;                 (wb (create-addr-bytes-alist l-addrs (byte-ify 2 word)) x86)))
;;             (mv flg x86))))
;;   :hints (("Goal"
;;            :in-theory (e/d* (all-paging-entries-found-p
;;                              mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
;;                              no-page-faults-during-translation-p
;;                              wm16
;;                              wm08
;;                              wb
;;                              byte-ify)
;;                             (signed-byte-p
;;                              unsigned-byte-p
;;                              bitops::logior-equal-0
;;                              wm08-to-wb-in-system-level-mode
;;                              (:meta acl2::mv-nth-cons-meta))))))

;; ;; ----------------------------------------------------------------------

;; (local
;;  (def-gl-thm rm32-rb-system-level-mode-proof-helper
;;    :hyp (and (n08p a)
;;              (n08p b)
;;              (n08p c)
;;              (n08p d))
;;    :concl (equal (logior a (ash b 8) (ash (logior c (ash d 8)) 16))
;;                  (logior a (ash (logior b (ash (logior c (ash d 8)) 8)) 8)))
;;    :g-bindings
;;    (gl::auto-bindings
;;     (:mix (:nat a 8) (:nat b 8) (:nat c 8) (:nat d 8)))))

;; (local (in-theory (e/d () (rm32-rb-system-level-mode-proof-helper))))

;; (defthmd rm32-to-rb-in-system-level-mode
;;   (implies
;;    (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
;;         (equal l-addrs (create-canonical-address-list 4 lin-addr))
;;         (equal (len l-addrs) 4)
;;         (all-paging-entries-found-p l-addrs (double-rewrite x86))
;;         (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p l-addrs r-w-x cpl (double-rewrite x86))
;;         (no-page-faults-during-translation-p l-addrs r-w-x cpl (double-rewrite x86)))
;;    (equal (rm32 lin-addr r-w-x x86)
;;           (b* (((mv flg bytes x86)
;;                 (rb l-addrs r-w-x x86))
;;                (result (combine-bytes bytes)))
;;             (mv flg result x86))))
;;   :hints (("Goal"
;;            :use ((:instance create-canonical-address-list-end-addr-is-canonical
;;                             (addr lin-addr)
;;                             (count 4)
;;                             (end-addr (+ 3 lin-addr))))
;;            :in-theory (e/d* (all-paging-entries-found-p
;;                              mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
;;                              no-page-faults-during-translation-p
;;                              rm32
;;                              rm08
;;                              rb
;;                              rm32-rb-system-level-mode-proof-helper)
;;                             (signed-byte-p
;;                              unsigned-byte-p
;;                              bitops::logior-equal-0
;;                              rm08-to-rb-in-system-level-mode
;;                              (:meta acl2::mv-nth-cons-meta)
;;                              mv-nth-1-rb-1-and-xlate-equiv-x86s-disjoint
;;                              force (force))))))

;; (defthmd wm32-to-wb-in-system-level-mode
;;   (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
;;                 (equal l-addrs (create-canonical-address-list 4 lin-addr))
;;                 (equal (len l-addrs) 4)
;;                 (all-paging-entries-found-p l-addrs (double-rewrite x86))
;;                 (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p l-addrs :w cpl (double-rewrite x86))
;;                 (no-page-faults-during-translation-p l-addrs :w cpl (double-rewrite x86)))
;;            (equal (wm32 lin-addr dword x86)
;;                   (b* (((mv flg x86)
;;                         (wb (create-addr-bytes-alist l-addrs (byte-ify 4 dword))
;;                             x86)))
;;                     (mv flg x86))))
;;   :hints (("Goal"
;;            :use ((:instance create-canonical-address-list-end-addr-is-canonical
;;                             (addr lin-addr)
;;                             (count 4)
;;                             (end-addr (+ 3 lin-addr))))
;;            :in-theory (e/d* (all-paging-entries-found-p
;;                              mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
;;                              no-page-faults-during-translation-p
;;                              wm32
;;                              wm08
;;                              wb
;;                              byte-ify)
;;                             ((:REWRITE ALL-PAGING-ENTRIES-FOUND-P-MEMBER-P)
;;                              (:REWRITE LOGHEAD-OF-NON-INTEGERP)
;;                              (:REWRITE CAR-CREATE-CANONICAL-ADDRESS-LIST)
;;                              (:REWRITE ACL2::LOGHEAD-IDENTITY)
;;                              (:REWRITE MEMBER-P-CANONICAL-ADDRESS-LISTP)
;;                              (:REWRITE DEFAULT-+-2)
;;                              (:REWRITE MEMBER-LIST-P-AND-PAIRWISE-DISJOINT-P-AUX)
;;                              (:REWRITE CANONICAL-ADDRESS-P-LIMITS-THM-3)
;;                              (:DEFINITION MEMBER-LIST-P)
;;                              (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP)
;;                              (:REWRITE DEFAULT-<-1)
;;                              (:TYPE-PRESCRIPTION SEG-VISIBLEI-IS-N16P)
;;                              (:DEFINITION OPEN-QWORD-PADDR-LIST-LIST)
;;                              (:REWRITE DEFAULT-+-1)
;;                              (:DEFINITION OPEN-QWORD-PADDR-LIST)
;;                              (:TYPE-PRESCRIPTION X86P)
;;                              (:TYPE-PRESCRIPTION CONSP-CREATE-ADDR-BYTES-ALIST)
;;                              (:TYPE-PRESCRIPTION BOOLEANP-PROGRAMMER-LEVEL-MODE-TYPE)
;;                              (:TYPE-PRESCRIPTION MEMBER-P)
;;                              (:REWRITE ACL2::LOGTAIL-IDENTITY)
;;                              (:REWRITE BITOPS::UNSIGNED-BYTE-P-WHEN-UNSIGNED-BYTE-P-LESS)
;;                              (:TYPE-PRESCRIPTION BITOPS::LOGTAIL-NATP)
;;                              (:REWRITE ACL2::CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP)
;;                              (:TYPE-PRESCRIPTION CONSP-CREATE-ADDR-BYTES-ALIST-IN-TERMS-OF-LEN)
;;                              (:REWRITE UNSIGNED-BYTE-P-OF-LOGTAIL)
;;                              (:DEFINITION BINARY-APPEND)
;;                              (:REWRITE MEMBER-P-CDR)
;;                              (:REWRITE OPEN-QWORD-PADDR-LIST-LIST-AND-MEMBER-LIST-P)
;;                              (:TYPE-PRESCRIPTION MEMBER-LIST-P)
;;                              (:REWRITE ACL2::APPEND-WHEN-NOT-CONSP)
;;                              (:TYPE-PRESCRIPTION NATP)
;;                              (:TYPE-PRESCRIPTION ACL2::LOGTAIL-TYPE)
;;                              (:REWRITE DEFAULT-<-2)
;;                              (:REWRITE ALL-SEG-VISIBLES-EQUAL-AUX-OPEN)
;;                              (:REWRITE CDR-CREATE-CANONICAL-ADDRESS-LIST)
;;                              (:REWRITE MEMBER-P-OF-NOT-A-CONSP)
;;                              (:DEFINITION ADDR-RANGE)
;;                              (:REWRITE ACL2::IFIX-WHEN-NOT-INTEGERP)
;;                              (:REWRITE ACL2::IFIX-WHEN-INTEGERP)
;;                              (:TYPE-PRESCRIPTION X86P-MV-NTH-1-WVM08)
;;                              (:REWRITE ACL2::CONSP-OF-CAR-WHEN-ATOM-LISTP)
;;                              (:REWRITE SUBSET-LIST-P-AND-MEMBER-LIST-P)
;;                              (:REWRITE CANONICAL-ADDRESS-P-LIMITS-THM-2)
;;                              (:REWRITE CANONICAL-ADDRESS-P-LIMITS-THM-1)
;;                              (:REWRITE CANONICAL-ADDRESS-P-LIMITS-THM-0)
;;                              (:TYPE-PRESCRIPTION TRUE-LISTP-ADDR-RANGE)
;;                              (:TYPE-PRESCRIPTION CONSP-ADDR-RANGE)
;;                              (:TYPE-PRESCRIPTION GATHER-ALL-PAGING-STRUCTURE-QWORD-ADDRESSES)
;;                              (:REWRITE PAIRWISE-DISJOINT-P-AUX-AND-APPEND)
;;                              (:TYPE-PRESCRIPTION XW)
;;                              (:REWRITE ACL2::EQUAL-OF-BOOLEANS-REWRITE)
;;                              (:REWRITE CAR-ADDR-RANGE)
;;                              (:TYPE-PRESCRIPTION ATOM-LISTP)
;;                              (:REWRITE DISJOINT-P-MEMBERS-OF-PAIRWISE-DISJOINT-P-AUX)
;;                              (:REWRITE SUBSET-P-CONS-MEMBER-P-LEMMA)
;;                              (:REWRITE MEMBER-LIST-P-NO-DUPLICATES-LIST-P-AND-MEMBER-P)
;;                              (:LINEAR MEMBER-P-POS-VALUE)
;;                              (:LINEAR MEMBER-P-POS-1-VALUE)
;;                              (:LINEAR ACL2::INDEX-OF-<-LEN)
;;                              (:TYPE-PRESCRIPTION MEMBER-P-PHYSICAL-ADDRESS-P-PHYSICAL-ADDRESS-LISTP)
;;                              (:REWRITE NO-PAGE-FAULTS-DURING-TRANSLATION-P-MEMBER-P)
;;                              (:TYPE-PRESCRIPTION IFIX)
;;                              (:REWRITE DISJOINT-P-SUBSET-P)
;;                              (:REWRITE DISJOINT-P-MEMBERS-OF-TRUE-LIST-LIST-DISJOINT-P)
;;                              (:REWRITE DISJOINT-P-MEMBERS-OF-PAIRWISE-DISJOINT-P)
;;                              (:REWRITE CDR-ADDR-RANGE)
;;                              (:TYPE-PRESCRIPTION N52P-MV-NTH-1-IA32E-ENTRIES-FOUND-LA-TO-PA)
;;                              (:REWRITE MAPPED-LIN-ADDRS-DISJOINT-FROM-PAGING-STRUCTURE-ADDRS-P-MEMBER-P)
;;                              (:REWRITE NO-PAGE-FAULTS-DURING-TRANSLATION-P-SUBSET-P)
;;                              (:REWRITE MAPPED-LIN-ADDRS-DISJOINT-FROM-PAGING-STRUCTURE-ADDRS-P-SUBSET-P)
;;                              (:REWRITE ALL-PAGING-ENTRIES-FOUND-P-SUBSET-P)
;;                              (:REWRITE MEMBER-P-AND-MULT-8-QWORD-PADDR-LISTP)
;;                              (:REWRITE MEMBER-LIST-P-AND-MULT-8-QWORD-PADDR-LIST-LISTP)
;;                              (:TYPE-PRESCRIPTION MEMBER-P-PHYSICAL-ADDRESS-P)
;;                              (:REWRITE XW-XW-INTRA-FIELD-ARRANGE-WRITES)
;;                              (:REWRITE XLATE-EQUIV-X86S-AND-XW-MEM-DISJOINT)
;;                              (:REWRITE CONSP-CREATE-ADDR-BYTES-ALIST-IN-TERMS-OF-LEN)
;;                              (:REWRITE XW-XW-INTRA-SIMPLE-FIELD-SHADOW-WRITES)
;;                              (:REWRITE IA32E-ENTRIES-FOUND-LA-TO-PA-XW-STATE)
;;                              (:LINEAR N52P-MV-NTH-1-IA32E-LA-TO-PA)
;;                              (:REWRITE X86P-MV-NTH-2-IA32E-LA-TO-PA)
;;                              (:DEFINITION MULT-8-QWORD-PADDR-LIST-LISTP)
;;                              (:DEFINITION MULT-8-QWORD-PADDR-LISTP)
;;                              (:LINEAR N52P-MV-NTH-1-IA32E-ENTRIES-FOUND-LA-TO-PA)
;;                              (:REWRITE LEN-OF-CREATE-CANONICAL-ADDRESS-LIST)
;;                              (:DEFINITION CANONICAL-ADDRESS-LISTP)
;;                              (:REWRITE CONSP-OF-CREATE-CANONICAL-ADDRESS-LIST)
;;                              (:TYPE-PRESCRIPTION N52P-MV-NTH-1-IA32E-LA-TO-PA)
;;                              (:LINEAR IA32E-LA-TO-PA-<-*MEM-SIZE-IN-BYTES-15*-WHEN-LOW-12-BITS-=-4081)
;;                              (:LINEAR IA32E-LA-TO-PA-<-*MEM-SIZE-IN-BYTES-15*-WHEN-LOW-12-BITS-<-4081)
;;                              (:LINEAR IA32E-LA-TO-PA-<-*MEM-SIZE-IN-BYTES-1*-WHEN-LOW-12-BITS-=-4090)
;;                              (:LINEAR IA32E-LA-TO-PA-<-*MEM-SIZE-IN-BYTES-1*-WHEN-LOW-12-BITS-=-4089)
;;                              (:LINEAR IA32E-LA-TO-PA-<-*MEM-SIZE-IN-BYTES-1*-WHEN-LOW-12-BITS-<-4093)
;;                              (:LINEAR IA32E-LA-TO-PA-<-*MEM-SIZE-IN-BYTES-1*-WHEN-LOW-12-BITS-<-4089)
;;                              (:LINEAR
;;                               IA32E-LA-TO-PA-<-*MEM-SIZE-IN-BYTES-1*-WHEN-LOW-12-BITS-!=-ALL-ONES)
;;                              (:REWRITE IA32E-ENTRIES-FOUND-LA-TO-PA-XW-VALUE)
;;                              (:LINEAR ACL2::LOGHEAD-UPPER-BOUND)
;;                              (:TYPE-PRESCRIPTION MEMBER-EQUAL)
;;                              (:TYPE-PRESCRIPTION XLATE-EQUIV-X86S)
;;                              (:REWRITE PHYSICAL-ADDRESS-P-LIMITS-THM-0)
;;                              (:TYPE-PRESCRIPTION MULT-8-QWORD-PADDR-LISTP)
;;                              (:REWRITE XLATE-EQUIV-X86S-AND-XW)
;;                              (:REWRITE GOOD-PAGING-STRUCTURES-X86P-XW-FLD!=MEM-AND-CTR)
;;                              (:REWRITE MULT-8-QWORD-PADDR-LIST-LISTP-AND-APPEND-2)
;;                              (:REWRITE MULT-8-QWORD-PADDR-LIST-LISTP-AND-APPEND-1)
;;                              (:REWRITE CANONICAL-ADDRESS-LISTP-FIRST-INPUT-TO-ALL-PAGING-ENTRIES-FOUND-P)
;;                              (:REWRITE GATHER-ALL-PAGING-STRUCTURE-QWORD-ADDRESSES-XW-FLD!=MEM-AND-CTR)
;;                              (:REWRITE PHYSICAL-ADDRESS-P-LIMITS-THM-3)
;;                              (:REWRITE PHYSICAL-ADDRESS-P-LIMITS-THM-2)
;;                              (:REWRITE PHYSICAL-ADDRESS-P-LIMITS-THM-1)
;;                              signed-byte-p
;;                              unsigned-byte-p
;;                              bitops::logior-equal-0
;;                              wm08-to-wb-in-system-level-mode
;;                              cons-equal
;;                              (:meta acl2::mv-nth-cons-meta)
;;                              force (force)
;;                              ia32e-la-to-pa-lower-12-bits-error
;;                              loghead-zero-smaller
;;                              ia32e-la-to-pa-lower-12-bits-value-of-address-when-error
;;                              good-paging-structures-x86p-implies-x86p)))))

;; ;; ----------------------------------------------------------------------

;; (local
;;  (def-gl-thm rm64-to-rb-in-system-level-mode-helper
;;    :hyp (and (n08p a) (n08p b) (n08p c) (n08p d)
;;              (n08p e) (n08p f) (n08p g) (n08p h))
;;    :concl (equal
;;            (logior a
;;                    (ash (logior b (ash (logior c (ash d 8)) 8)) 8)
;;                    (ash (logior e (ash (logior f (ash (logior g (ash h 8)) 8)) 8)) 32))
;;            (logior
;;             a
;;             (ash (logior
;;                   b
;;                   (ash (logior
;;                         c
;;                         (ash (logior d
;;                                      (ash
;;                                       (logior e
;;                                               (ash
;;                                                (logior f
;;                                                        (ash (logior g (ash h 8)) 8)) 8)) 8)) 8)) 8)) 8)))
;;    :g-bindings
;;    (gl::auto-bindings
;;     (:mix (:nat a 8) (:nat b 8) (:nat c 8) (:nat d 8)
;;           (:nat e 8) (:nat f 8) (:nat g 8) (:nat h 8)))
;;    :rule-classes :linear))

;; (local (in-theory (e/d () (rm64-to-rb-in-system-level-mode-helper))))

;; (defthmd rm64-to-rb-in-system-level-mode
;;   ;; TO-DO: Speed this up.
;;   (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
;;                 (equal l-addrs (create-canonical-address-list 8 lin-addr))
;;                 (equal (len l-addrs) 8)
;;                 (all-paging-entries-found-p l-addrs (double-rewrite x86))
;;                 (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p l-addrs r-w-x cpl (double-rewrite x86))
;;                 (no-page-faults-during-translation-p l-addrs r-w-x cpl (double-rewrite x86)))
;;            (equal (rm64 lin-addr r-w-x x86)
;;                   (b* (((mv flg bytes x86)
;;                         (rb l-addrs r-w-x x86))
;;                        (result (combine-bytes bytes)))
;;                     (mv flg result x86))))
;;   :hints (("Goal"
;;            :use ((:instance create-canonical-address-list-end-addr-is-canonical
;;                             (addr lin-addr)
;;                             (count 8)
;;                             (end-addr (+ 7 lin-addr))))
;;            :in-theory (e/d* (all-paging-entries-found-p
;;                              mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
;;                              no-page-faults-during-translation-p
;;                              rm32-to-rb-in-system-level-mode
;;                              rm64-to-rb-in-system-level-mode-helper
;;                              rm64
;;                              rm08
;;                              rb)
;;                             ((:LINEAR BITOPS::LOGIOR-<-0-LINEAR-2)
;;                              (:LINEAR ASH-MONOTONE-2)
;;                              (:REWRITE ACL2::NATP-WHEN-INTEGERP)
;;                              (:REWRITE BITOPS::ASH-<-0)
;;                              (:REWRITE ACL2::ASH-0)
;;                              (:REWRITE ACL2::ZIP-OPEN)
;;                              (:TYPE-PRESCRIPTION BITOPS::LOGIOR-NATP-TYPE)
;;                              (:TYPE-PRESCRIPTION BITOPS::ASH-NATP-TYPE)
;;                              (:TYPE-PRESCRIPTION MEMI-IS-N08P)
;;                              (:TYPE-PRESCRIPTION N08P-MV-NTH-1-RVM08)
;;                              (:REWRITE ACL2::NATP-WHEN-GTE-0)
;;                              (:REWRITE ACL2::IFIX-NEGATIVE-TO-NEGP)
;;                              (:LINEAR <=-LOGIOR)
;;                              (:DEFINITION OPEN-QWORD-PADDR-LIST-LIST)
;;                              (:REWRITE MEMBER-LIST-P-AND-PAIRWISE-DISJOINT-P-AUX)
;;                              (:TYPE-PRESCRIPTION N52P-MV-NTH-1-IA32E-ENTRIES-FOUND-LA-TO-PA)
;;                              (:DEFINITION OPEN-QWORD-PADDR-LIST)
;;                              (:LINEAR BITOPS::LOGIOR->=-0-LINEAR)
;;                              (:LINEAR BITOPS::LOGIOR-<-0-LINEAR-1)
;;                              (:REWRITE LOGHEAD-OF-NON-INTEGERP)
;;                              (:REWRITE ACL2::LOGHEAD-IDENTITY)
;;                              (:REWRITE DEFAULT-<-1)
;;                              (:REWRITE LOGHEAD-ZERO-SMALLER)
;;                              (:REWRITE ALL-SEG-VISIBLES-EQUAL-AUX-OPEN)
;;                              (:REWRITE ACL2::IFIX-WHEN-NOT-INTEGERP)
;;                              (:REWRITE ACL2::IFIX-WHEN-INTEGERP)
;;                              (:DEFINITION MEMBER-LIST-P)
;;                              (:REWRITE ACL2::NEGP-WHEN-LESS-THAN-0)
;;                              (:REWRITE DEFAULT-+-2)
;;                              (:REWRITE DEFAULT-+-1)
;;                              (:DEFINITION BINARY-APPEND)
;;                              (:REWRITE ACL2::CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP)
;;                              (:REWRITE ACL2::APPEND-WHEN-NOT-CONSP)
;;                              (:REWRITE ACL2::NEGP-WHEN-INTEGERP)
;;                              (:TYPE-PRESCRIPTION ASH)
;;                              (:REWRITE DEFAULT-<-2)
;;                              (:DEFINITION ADDR-RANGE)
;;                              (:TYPE-PRESCRIPTION MEMBER-LIST-P)
;;                              (:TYPE-PRESCRIPTION MEMBER-P)
;;                              (:REWRITE OPEN-QWORD-PADDR-LIST-LIST-AND-MEMBER-LIST-P)
;;                              (:REWRITE MEMBER-P-OF-NOT-A-CONSP)
;;                              (:TYPE-PRESCRIPTION IFIX)
;;                              (:DEFINITION BYTE-LISTP)
;;                              (:LINEAR N08P-MV-NTH-1-RVM08)
;;                              (:TYPE-PRESCRIPTION TRUE-LISTP-ADDR-RANGE)
;;                              (:TYPE-PRESCRIPTION CONSP-ADDR-RANGE)
;;                              (:REWRITE MEMBER-P-CDR)
;;                              (:REWRITE DISJOINT-P-MEMBERS-OF-PAIRWISE-DISJOINT-P-AUX)
;;                              (:REWRITE ACL2::CONSP-OF-CAR-WHEN-ATOM-LISTP)
;;                              (:REWRITE PAIRWISE-DISJOINT-P-AUX-AND-APPEND)
;;                              (:TYPE-PRESCRIPTION NATP)
;;                              (:REWRITE CAR-ADDR-RANGE)
;;                              (:REWRITE SUBSET-LIST-P-AND-MEMBER-LIST-P)
;;                              (:TYPE-PRESCRIPTION GATHER-ALL-PAGING-STRUCTURE-QWORD-ADDRESSES)
;;                              (:DEFINITION MULT-8-QWORD-PADDR-LIST-LISTP)
;;                              (:LINEAR MEMI-IS-N08P)
;;                              (:TYPE-PRESCRIPTION ATOM-LISTP)
;;                              (:TYPE-PRESCRIPTION MEMBER-P-PHYSICAL-ADDRESS-P-PHYSICAL-ADDRESS-LISTP)
;;                              (:DEFINITION MULT-8-QWORD-PADDR-LISTP)
;;                              (:LINEAR UNSIGNED-BYTE-P-OF-COMBINE-BYTES)
;;                              (:TYPE-PRESCRIPTION SEG-VISIBLEI-IS-N16P)
;;                              (:REWRITE ALL-PAGING-ENTRIES-FOUND-P-MEMBER-P)
;;                              (:REWRITE BITOPS::UNSIGNED-BYTE-P-WHEN-UNSIGNED-BYTE-P-LESS)
;;                              (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP)
;;                              (:TYPE-PRESCRIPTION NEGP)
;;                              (:LINEAR SIZE-OF-COMBINE-BYTES)
;;                              (:REWRITE MEMBER-P-AND-MULT-8-QWORD-PADDR-LISTP)
;;                              (:REWRITE MEMBER-LIST-P-AND-MULT-8-QWORD-PADDR-LIST-LISTP)
;;                              (:REWRITE SUBSET-P-CONS-MEMBER-P-LEMMA)
;;                              (:REWRITE MEMBER-LIST-P-NO-DUPLICATES-LIST-P-AND-MEMBER-P)
;;                              (:TYPE-PRESCRIPTION MEMBER-P-PHYSICAL-ADDRESS-P)
;;                              (:REWRITE MAPPED-LIN-ADDRS-DISJOINT-FROM-PAGING-STRUCTURE-ADDRS-P-MEMBER-P)
;;                              (:REWRITE DISJOINT-P-SUBSET-P)
;;                              (:REWRITE DISJOINT-P-MEMBERS-OF-TRUE-LIST-LIST-DISJOINT-P)
;;                              (:REWRITE DISJOINT-P-MEMBERS-OF-PAIRWISE-DISJOINT-P)
;;                              (:REWRITE CDR-ADDR-RANGE)
;;                              (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P)
;;                              (:REWRITE CONSTANT-UPPER-BOUND-OF-LOGIOR-FOR-NATURALS)
;;                              (:REWRITE ALL-MEM-EXCEPT-PAGING-STRUCTURES-EQUAL-AUX-OPEN)
;;                              (:REWRITE CANONICAL-ADDRESS-P-LIMITS-THM-3)
;;                              (:LINEAR BITOPS::UPPER-BOUND-OF-LOGIOR-FOR-NATURALS)
;;                              (:REWRITE CANONICAL-ADDRESS-P-LIMITS-THM-2)
;;                              (:REWRITE CANONICAL-ADDRESS-P-LIMITS-THM-1)
;;                              (:REWRITE CANONICAL-ADDRESS-P-LIMITS-THM-0)
;;                              (:REWRITE CANONICAL-ADDRESS-LISTP-FIRST-INPUT-TO-ALL-PAGING-ENTRIES-FOUND-P)
;;                              (:TYPE-PRESCRIPTION BYTE-LISTP)
;;                              (:REWRITE NO-PAGE-FAULTS-DURING-TRANSLATION-P-MEMBER-P)
;;                              (:REWRITE ACL2::EQUAL-OF-BOOLEANS-REWRITE)
;;                              (:REWRITE
;;                               GOOD-PAGING-STRUCTURES-X86P-IMPLIES-MULT-8-QWORD-PADDR-LIST-LISTP-PAGING-STRUCTURE-ADDRS)
;;                              (:TYPE-PRESCRIPTION NATP-COMBINE-BYTES)
;;                              (:REWRITE N08P-MV-NTH-1-RVM08)
;;                              (:TYPE-PRESCRIPTION MULT-8-QWORD-PADDR-LIST-LISTP)
;;                              (:LINEAR ACL2::LOGHEAD-UPPER-BOUND)
;;                              (:REWRITE MEMBER-P-CANONICAL-ADDRESS-LISTP)
;;                              (:REWRITE PHYSICAL-ADDRESS-P-LIMITS-THM-0)
;;                              (:TYPE-PRESCRIPTION MULT-8-QWORD-PADDR-LISTP)
;;                              (:REWRITE MAPPED-LIN-ADDRS-DISJOINT-FROM-PAGING-STRUCTURE-ADDRS-P-SUBSET-P)
;;                              (:REWRITE MULT-8-QWORD-PADDR-LIST-LISTP-AND-APPEND-2)
;;                              (:REWRITE MULT-8-QWORD-PADDR-LIST-LISTP-AND-APPEND-1)
;;                              (:REWRITE RIGHT-SHIFT-TO-LOGTAIL)
;;                              (:REWRITE PHYSICAL-ADDRESS-P-LIMITS-THM-3)
;;                              (:REWRITE PHYSICAL-ADDRESS-P-LIMITS-THM-2)
;;                              (:REWRITE PHYSICAL-ADDRESS-P-LIMITS-THM-1)
;;                              (:REWRITE SUBSET-P-CDR-Y)
;;                              (:REWRITE ACL2::REDUCE-INTEGERP-+-CONSTANT)
;;                              (:TYPE-PRESCRIPTION ZIP)
;;                              (:DEFINITION FIX)
;;                              (:LINEAR N32P-MV-NTH-1-RM32)
;;                              (:REWRITE SUBSET-P-TWO-CREATE-CANONICAL-ADDRESS-LISTS-SAME-BASE-ADDRESS)
;;                              (:REWRITE CONSP-OF-CREATE-CANONICAL-ADDRESS-LIST)
;;                              (:REWRITE CDR-CREATE-CANONICAL-ADDRESS-LIST)
;;                              (:REWRITE LEN-OF-CREATE-CANONICAL-ADDRESS-LIST)
;;                              (:TYPE-PRESCRIPTION X86P-RM32)
;;                              (:REWRITE CAR-CREATE-CANONICAL-ADDRESS-LIST)
;;                              (:REWRITE X86P-RM32)
;;                              (:REWRITE SUBSET-P-TWO-CREATE-CANONICAL-ADDRESS-LISTS-GENERAL)
;;                              (:TYPE-PRESCRIPTION BOOLEANP)
;;                              (:TYPE-PRESCRIPTION N32P-MV-NTH-1-RM32)
;;                              (:LINEAR MEMBER-P-POS-VALUE)
;;                              (:LINEAR MEMBER-P-POS-1-VALUE)
;;                              (:LINEAR ACL2::INDEX-OF-<-LEN)
;;                              (:REWRITE RB-1-RETURNS-X86-PROGRAMMER-LEVEL-MODE)
;;                              (:REWRITE BITOPS::LOGIOR-FOLD-CONSTS)
;;                              (:REWRITE RB-1-ACCUMULATOR-THM)
;;                              signed-byte-p
;;                              unsigned-byte-p
;;                              bitops::logior-equal-0
;;                              rm08-to-rb-in-system-level-mode
;;                              (:meta acl2::mv-nth-cons-meta)
;;                              mv-nth-1-rb-1-and-xlate-equiv-x86s-disjoint
;;                              force (force))))))

;; (defthmd wm64-to-wb-in-system-level-mode
;;   ;; TO-DO: Speed this up.
;;   (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
;;                 (equal l-addrs (create-canonical-address-list 8 lin-addr))
;;                 (equal (len l-addrs) 8)
;;                 (all-paging-entries-found-p l-addrs x86)
;;                 (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p l-addrs :w cpl x86)
;;                 (no-page-faults-during-translation-p l-addrs :w cpl x86))
;;            (equal (wm64 lin-addr qword x86)
;;                   (b* (((mv flg x86)
;;                         (wb (create-addr-bytes-alist l-addrs (byte-ify 8 qword))
;;                             x86)))
;;                     (mv flg x86))))
;;   :hints (("Goal"
;;            :use ((:instance create-canonical-address-list-end-addr-is-canonical
;;                             (addr lin-addr)
;;                             (count 8)
;;                             (end-addr (+ 7 lin-addr))))
;;            :in-theory (e/d* (all-paging-entries-found-p
;;                              mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
;;                              no-page-faults-during-translation-p
;;                              wm64 wm32 wm08 wb
;;                              byte-ify)
;;                             ((:REWRITE ALL-PAGING-ENTRIES-FOUND-P-MEMBER-P)
;;                              (:REWRITE LOGHEAD-OF-NON-INTEGERP)
;;                              (:REWRITE CAR-CREATE-CANONICAL-ADDRESS-LIST)
;;                              (:REWRITE ACL2::LOGHEAD-IDENTITY)
;;                              (:REWRITE MEMBER-P-CANONICAL-ADDRESS-LISTP)
;;                              (:REWRITE DEFAULT-+-2)
;;                              (:REWRITE MEMBER-LIST-P-AND-PAIRWISE-DISJOINT-P-AUX)
;;                              (:REWRITE CANONICAL-ADDRESS-P-LIMITS-THM-3)
;;                              (:DEFINITION MEMBER-LIST-P)
;;                              (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP)
;;                              (:REWRITE DEFAULT-<-1)
;;                              (:TYPE-PRESCRIPTION SEG-VISIBLEI-IS-N16P)
;;                              (:DEFINITION OPEN-QWORD-PADDR-LIST-LIST)
;;                              (:REWRITE DEFAULT-+-1)
;;                              (:DEFINITION OPEN-QWORD-PADDR-LIST)
;;                              (:TYPE-PRESCRIPTION X86P)
;;                              (:TYPE-PRESCRIPTION CONSP-CREATE-ADDR-BYTES-ALIST)
;;                              (:TYPE-PRESCRIPTION BOOLEANP-PROGRAMMER-LEVEL-MODE-TYPE)
;;                              (:TYPE-PRESCRIPTION MEMBER-P)
;;                              (:REWRITE ACL2::LOGTAIL-IDENTITY)
;;                              (:REWRITE BITOPS::UNSIGNED-BYTE-P-WHEN-UNSIGNED-BYTE-P-LESS)
;;                              (:TYPE-PRESCRIPTION BITOPS::LOGTAIL-NATP)
;;                              (:REWRITE ACL2::CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP)
;;                              (:TYPE-PRESCRIPTION CONSP-CREATE-ADDR-BYTES-ALIST-IN-TERMS-OF-LEN)
;;                              (:REWRITE UNSIGNED-BYTE-P-OF-LOGTAIL)
;;                              (:DEFINITION BINARY-APPEND)
;;                              (:REWRITE MEMBER-P-CDR)
;;                              (:REWRITE OPEN-QWORD-PADDR-LIST-LIST-AND-MEMBER-LIST-P)
;;                              (:TYPE-PRESCRIPTION MEMBER-LIST-P)
;;                              (:REWRITE ACL2::APPEND-WHEN-NOT-CONSP)
;;                              (:TYPE-PRESCRIPTION NATP)
;;                              (:TYPE-PRESCRIPTION ACL2::LOGTAIL-TYPE)
;;                              (:REWRITE DEFAULT-<-2)
;;                              (:REWRITE ALL-SEG-VISIBLES-EQUAL-AUX-OPEN)
;;                              (:REWRITE CDR-CREATE-CANONICAL-ADDRESS-LIST)
;;                              (:REWRITE MEMBER-P-OF-NOT-A-CONSP)
;;                              (:DEFINITION ADDR-RANGE)
;;                              (:REWRITE ACL2::IFIX-WHEN-NOT-INTEGERP)
;;                              (:REWRITE ACL2::IFIX-WHEN-INTEGERP)
;;                              (:TYPE-PRESCRIPTION X86P-MV-NTH-1-WVM08)
;;                              (:REWRITE ACL2::CONSP-OF-CAR-WHEN-ATOM-LISTP)
;;                              (:REWRITE SUBSET-LIST-P-AND-MEMBER-LIST-P)
;;                              (:REWRITE CANONICAL-ADDRESS-P-LIMITS-THM-2)
;;                              (:REWRITE CANONICAL-ADDRESS-P-LIMITS-THM-1)
;;                              (:REWRITE CANONICAL-ADDRESS-P-LIMITS-THM-0)
;;                              (:TYPE-PRESCRIPTION TRUE-LISTP-ADDR-RANGE)
;;                              (:TYPE-PRESCRIPTION CONSP-ADDR-RANGE)
;;                              (:TYPE-PRESCRIPTION GATHER-ALL-PAGING-STRUCTURE-QWORD-ADDRESSES)
;;                              (:REWRITE PAIRWISE-DISJOINT-P-AUX-AND-APPEND)
;;                              (:TYPE-PRESCRIPTION XW)
;;                              (:REWRITE ACL2::EQUAL-OF-BOOLEANS-REWRITE)
;;                              (:REWRITE CAR-ADDR-RANGE)
;;                              (:TYPE-PRESCRIPTION ATOM-LISTP)
;;                              (:REWRITE DISJOINT-P-MEMBERS-OF-PAIRWISE-DISJOINT-P-AUX)
;;                              (:REWRITE SUBSET-P-CONS-MEMBER-P-LEMMA)
;;                              (:REWRITE MEMBER-LIST-P-NO-DUPLICATES-LIST-P-AND-MEMBER-P)
;;                              (:LINEAR MEMBER-P-POS-VALUE)
;;                              (:LINEAR MEMBER-P-POS-1-VALUE)
;;                              (:LINEAR ACL2::INDEX-OF-<-LEN)
;;                              (:TYPE-PRESCRIPTION MEMBER-P-PHYSICAL-ADDRESS-P-PHYSICAL-ADDRESS-LISTP)
;;                              (:REWRITE NO-PAGE-FAULTS-DURING-TRANSLATION-P-MEMBER-P)
;;                              (:TYPE-PRESCRIPTION IFIX)
;;                              (:REWRITE DISJOINT-P-SUBSET-P)
;;                              (:REWRITE DISJOINT-P-MEMBERS-OF-TRUE-LIST-LIST-DISJOINT-P)
;;                              (:REWRITE DISJOINT-P-MEMBERS-OF-PAIRWISE-DISJOINT-P)
;;                              (:REWRITE CDR-ADDR-RANGE)
;;                              (:TYPE-PRESCRIPTION N52P-MV-NTH-1-IA32E-ENTRIES-FOUND-LA-TO-PA)
;;                              (:REWRITE MAPPED-LIN-ADDRS-DISJOINT-FROM-PAGING-STRUCTURE-ADDRS-P-MEMBER-P)
;;                              (:REWRITE NO-PAGE-FAULTS-DURING-TRANSLATION-P-SUBSET-P)
;;                              (:REWRITE MAPPED-LIN-ADDRS-DISJOINT-FROM-PAGING-STRUCTURE-ADDRS-P-SUBSET-P)
;;                              (:REWRITE ALL-PAGING-ENTRIES-FOUND-P-SUBSET-P)
;;                              (:REWRITE MEMBER-P-AND-MULT-8-QWORD-PADDR-LISTP)
;;                              (:REWRITE MEMBER-LIST-P-AND-MULT-8-QWORD-PADDR-LIST-LISTP)
;;                              (:TYPE-PRESCRIPTION MEMBER-P-PHYSICAL-ADDRESS-P)
;;                              (:REWRITE XW-XW-INTRA-FIELD-ARRANGE-WRITES)
;;                              (:REWRITE XLATE-EQUIV-X86S-AND-XW-MEM-DISJOINT)
;;                              (:REWRITE CONSP-CREATE-ADDR-BYTES-ALIST-IN-TERMS-OF-LEN)
;;                              (:REWRITE XW-XW-INTRA-SIMPLE-FIELD-SHADOW-WRITES)
;;                              (:REWRITE IA32E-ENTRIES-FOUND-LA-TO-PA-XW-STATE)
;;                              (:LINEAR N52P-MV-NTH-1-IA32E-LA-TO-PA)
;;                              (:REWRITE X86P-MV-NTH-2-IA32E-LA-TO-PA)
;;                              (:DEFINITION MULT-8-QWORD-PADDR-LIST-LISTP)
;;                              (:DEFINITION MULT-8-QWORD-PADDR-LISTP)
;;                              (:LINEAR N52P-MV-NTH-1-IA32E-ENTRIES-FOUND-LA-TO-PA)
;;                              (:REWRITE LEN-OF-CREATE-CANONICAL-ADDRESS-LIST)
;;                              (:DEFINITION CANONICAL-ADDRESS-LISTP)
;;                              (:REWRITE CONSP-OF-CREATE-CANONICAL-ADDRESS-LIST)
;;                              (:TYPE-PRESCRIPTION N52P-MV-NTH-1-IA32E-LA-TO-PA)
;;                              (:LINEAR IA32E-LA-TO-PA-<-*MEM-SIZE-IN-BYTES-15*-WHEN-LOW-12-BITS-=-4081)
;;                              (:LINEAR IA32E-LA-TO-PA-<-*MEM-SIZE-IN-BYTES-15*-WHEN-LOW-12-BITS-<-4081)
;;                              (:LINEAR IA32E-LA-TO-PA-<-*MEM-SIZE-IN-BYTES-1*-WHEN-LOW-12-BITS-=-4090)
;;                              (:LINEAR IA32E-LA-TO-PA-<-*MEM-SIZE-IN-BYTES-1*-WHEN-LOW-12-BITS-=-4089)
;;                              (:LINEAR IA32E-LA-TO-PA-<-*MEM-SIZE-IN-BYTES-1*-WHEN-LOW-12-BITS-<-4093)
;;                              (:LINEAR IA32E-LA-TO-PA-<-*MEM-SIZE-IN-BYTES-1*-WHEN-LOW-12-BITS-<-4089)
;;                              (:LINEAR
;;                               IA32E-LA-TO-PA-<-*MEM-SIZE-IN-BYTES-1*-WHEN-LOW-12-BITS-!=-ALL-ONES)
;;                              (:REWRITE IA32E-ENTRIES-FOUND-LA-TO-PA-XW-VALUE)
;;                              (:LINEAR ACL2::LOGHEAD-UPPER-BOUND)
;;                              (:TYPE-PRESCRIPTION MEMBER-EQUAL)
;;                              (:TYPE-PRESCRIPTION XLATE-EQUIV-X86S)
;;                              (:REWRITE PHYSICAL-ADDRESS-P-LIMITS-THM-0)
;;                              (:TYPE-PRESCRIPTION MULT-8-QWORD-PADDR-LISTP)
;;                              (:REWRITE XLATE-EQUIV-X86S-AND-XW)
;;                              (:REWRITE GOOD-PAGING-STRUCTURES-X86P-XW-FLD!=MEM-AND-CTR)
;;                              (:REWRITE MULT-8-QWORD-PADDR-LIST-LISTP-AND-APPEND-2)
;;                              (:REWRITE MULT-8-QWORD-PADDR-LIST-LISTP-AND-APPEND-1)
;;                              (:REWRITE CANONICAL-ADDRESS-LISTP-FIRST-INPUT-TO-ALL-PAGING-ENTRIES-FOUND-P)
;;                              (:REWRITE GATHER-ALL-PAGING-STRUCTURE-QWORD-ADDRESSES-XW-FLD!=MEM-AND-CTR)
;;                              (:REWRITE PHYSICAL-ADDRESS-P-LIMITS-THM-3)
;;                              (:REWRITE PHYSICAL-ADDRESS-P-LIMITS-THM-2)
;;                              (:REWRITE PHYSICAL-ADDRESS-P-LIMITS-THM-1)
;;                              signed-byte-p
;;                              unsigned-byte-p
;;                              bitops::logior-equal-0
;;                              wm08-to-wb-in-system-level-mode
;;                              mv-nth-1-wm08-and-xlate-equiv-structures-disjoint
;;                              wm32-to-wb-in-system-level-mode
;;                              cons-equal
;;                              (:meta acl2::mv-nth-cons-meta)
;;                              force (force))))))

;; ======================================================================

;; RoW theorems in terms of rb and wb:

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
                    nil))))

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

(defthm translate-all-l-addrs-member-p-lemma
  (implies (and (disjoint-p (translate-all-l-addrs l-addrs-1 r-w-x-1 cpl x86)
                            (translate-all-l-addrs l-addrs-2 r-w-x-2 cpl x86))
                (member-p index l-addrs-1))
           (disjoint-p
            (list (mv-nth 1 (ia32e-entries-found-la-to-pa index r-w-x-1 cpl x86)))
            (translate-all-l-addrs l-addrs-2 r-w-x-2 cpl x86)))
  :hints (("Goal"
           :induct (translate-all-l-addrs l-addrs-1 r-w-x-1 cpl x86)
           :in-theory (e/d* (disjoint-p member-p) ()))))

(local
 (DEFTHM RB-1-WB-DISJOINT-IN-SYSTEM-LEVEL-MODE-1-2-5
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
   (IMPLIES
    (AND
     (CONSP L-ADDRS-1)
     (EQUAL
      (MV-NTH 1
              (RB-1 (CDR L-ADDRS-1)
                    R-W-X
                    (MV-NTH 1
                            (WB ADDR-BYTES
                                (MV-NTH 2 (RM08 (CAR L-ADDRS-1) R-W-X X86))))
                    NIL))
      (MV-NTH 1 (RB-1 (CDR L-ADDRS-1) R-W-X X86 NIL)))
     (PAGING-ENTRIES-FOUND-P (CAR L-ADDRS-1)
                             X86)
     (ALL-PAGING-ENTRIES-FOUND-P (CDR L-ADDRS-1)
                                 X86)
     (ALL-PAGING-ENTRIES-FOUND-P (STRIP-CARS ADDR-BYTES)
                                 X86)
     (DISJOINT-P (TRANSLATE-ALL-L-ADDRS L-ADDRS-1 R-W-X
                                        (LOGHEAD 2 (XR :SEG-VISIBLE 1 X86))
                                        X86)
                 (TRANSLATE-ALL-L-ADDRS (STRIP-CARS ADDR-BYTES)
                                        :W (LOGHEAD 2 (XR :SEG-VISIBLE 1 X86))
                                        X86))
     (PAIRWISE-DISJOINT-P-AUX
      (LIST
       (MV-NTH
        1
        (IA32E-ENTRIES-FOUND-LA-TO-PA (CAR L-ADDRS-1)
                                      R-W-X
                                      (LOGHEAD 2 (XR :SEG-VISIBLE 1 X86))
                                      X86)))
      (OPEN-QWORD-PADDR-LIST-LIST
       (GATHER-ALL-PAGING-STRUCTURE-QWORD-ADDRESSES X86)))
     (MAPPED-LIN-ADDRS-DISJOINT-FROM-PAGING-STRUCTURE-ADDRS-P
      (CDR L-ADDRS-1)
      R-W-X
      (LOGHEAD 2 (XR :SEG-VISIBLE 1 X86))
      X86)
     (MAPPED-LIN-ADDRS-DISJOINT-FROM-PAGING-STRUCTURE-ADDRS-P
      (STRIP-CARS ADDR-BYTES)
      :W (LOGHEAD 2 (XR :SEG-VISIBLE 1 X86))
      X86)
     (TRUE-LISTP ACC)
     (NOT (MV-NTH 0 (RM08 (CAR L-ADDRS-1) R-W-X X86))))
    (EQUAL (MV-NTH 1
                   (RB-1 L-ADDRS-1
                         R-W-X (MV-NTH 1 (WB ADDR-BYTES X86))
                         NIL))
           (CONS (MV-NTH 1 (RM08 (CAR L-ADDRS-1) R-W-X X86))
                 (MV-NTH 1
                         (RB-1 (CDR L-ADDRS-1) R-W-X X86 NIL)))))
   :INSTRUCTIONS
   ((:DV 2 1 2)
    :X :TOP :BASH (:DV 1)
    (:REWRITE RM08-AND-WB-DISJOINT-LEMMA
              ((CPL (BITOPS::PART-SELECT-WIDTH-LOW (SEG-VISIBLEI 1 X86)
                                                   2 0))))
    :TOP
    :BASH :BASH :BASH :DEMOTE (:DV 1 6 1)
    :X :UP :S
    :TOP (:IN-THEORY (E/D (DISJOINT-P) NIL))
    :BASH :BASH :BASH (:DV 1)
    (:REWRITE RM08-AND-WB-DISJOINT-LEMMA
              ((CPL (BITOPS::PART-SELECT-WIDTH-LOW (SEG-VISIBLEI 1 X86)
                                                   2 0))))
    :TOP
    :BASH :BASH :BASH :DEMOTE (:DV 1 6 1)
    :X
    :TOP (:IN-THEORY (E/D (DISJOINT-P) NIL))
    :BASH :BASH :BASH
    (:IN-THEORY (E/D NIL
                     (MV-NTH-1-RB-1-AND-XLATE-EQUIV-X86S-DISJOINT)))
    (:USE
     (:INSTANCE MV-NTH-1-RB-1-AND-XLATE-EQUIV-X86S-DISJOINT
                (L-ADDRS (CDR L-ADDRS-1))
                (R-W-X R-W-X)
                (X86-1 (MV-NTH 2
                               (RM08 (CAR L-ADDRS-1)
                                     R-W-X (MV-NTH 1 (WB ADDR-BYTES X86)))))
                (X86-2 (MV-NTH 1 (WB ADDR-BYTES X86)))
                (ACC NIL))
     (:INSTANCE
      MV-NTH-1-RB-1-AND-XLATE-EQUIV-X86S-DISJOINT
      (L-ADDRS (CDR L-ADDRS-1))
      (R-W-X R-W-X)
      (X86-1 (MV-NTH 1
                     (WB ADDR-BYTES
                         (MV-NTH 2 (RM08 (CAR L-ADDRS-1) R-W-X X86)))))
      (X86-2 (MV-NTH 1 (WB ADDR-BYTES X86)))
      (ACC NIL)))
    :BASH)))

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
                             wb
                             rm08-wm08-disjoint-in-system-level-mode
                             all-paging-entries-found-p
                             mapped-lin-addrs-disjoint-from-paging-structure-addrs-p)
                            (signed-byte-p unsigned-byte-p)))
          ("Subgoal *1/2.4'"
           :in-theory (e/d* (rb-1
                             wb
                             rm08-wm08-disjoint-in-system-level-mode
                             all-paging-entries-found-p
                             mapped-lin-addrs-disjoint-from-paging-structure-addrs-p)
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

;; (i-am-here)

(defthm rm08-from-linear-addresses-that-map-to-the-same-physical-address
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

(defthm wm08-from-linear-addresses-that-map-to-the-same-physical-address
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

(local
 (DEFTHMD RM08-AND-WB-MEMBER-LEMMA-ERROR-HELPER
   (IMPLIES
    (AND
     (CONSP ADDR-BYTES)
     (EQUAL
      (MV-NTH 1
              (IA32E-ENTRIES-FOUND-LA-TO-PA INDEX R-W-X
                                            (LOGHEAD 2 (XR :SEG-VISIBLE 1 X86))
                                            X86))
      (MV-NTH
       1
       (IA32E-ENTRIES-FOUND-LA-TO-PA (CAR (STRIP-CARS ADDR-BYTES))
                                     :W (LOGHEAD 2 (XR :SEG-VISIBLE 1 X86))
                                     X86)))
     (PAGING-ENTRIES-FOUND-P INDEX X86)
     (ALL-PAGING-ENTRIES-FOUND-P (STRIP-CARS ADDR-BYTES)
                                 X86)
     (CONSP (STRIP-CARS ADDR-BYTES))
     (NO-DUPLICATES-P
      (TRANSLATE-ALL-L-ADDRS (STRIP-CARS ADDR-BYTES)
                             :W (LOGHEAD 2 (XR :SEG-VISIBLE 1 X86))
                             X86))
     (NO-DUPLICATES-P (STRIP-CARS ADDR-BYTES))
     (MAPPED-LIN-ADDRS-DISJOINT-FROM-PAGING-STRUCTURE-ADDRS-P
      (STRIP-CARS ADDR-BYTES)
      :W (LOGHEAD 2 (XR :SEG-VISIBLE 1 X86))
      X86)
     (NOT
      (MV-NTH 0
              (IA32E-ENTRIES-FOUND-LA-TO-PA INDEX R-W-X
                                            (LOGHEAD 2 (XR :SEG-VISIBLE 1 X86))
                                            X86)))
     (NO-PAGE-FAULTS-DURING-TRANSLATION-P
      (STRIP-CARS ADDR-BYTES)
      :W (LOGHEAD 2 (XR :SEG-VISIBLE 1 X86))
      X86)
     (ADDR-BYTE-ALISTP ADDR-BYTES))
    (NOT (MV-NTH 0
                 (RM08 INDEX
                       R-W-X (MV-NTH 1 (WB ADDR-BYTES X86))))))
   :INSTRUCTIONS
   ((:DV 2 1 2 3 2)
    :X :TOP
    (:IN-THEORY
     (E/D (NO-PAGE-FAULTS-DURING-TRANSLATION-P
           MAPPED-LIN-ADDRS-DISJOINT-FROM-PAGING-STRUCTURE-ADDRS-P
           ALL-PAGING-ENTRIES-FOUND-P
           POS RM08-WM08-EQUAL-IN-SYSTEM-LEVEL-MODE
           DISJOINT-P)
          NIL))
    :BASH (:DV 1)
    (:REWRITE RM08-AND-WB-DISJOINT-LEMMA
              ((CPL (BITOPS::PART-SELECT-WIDTH-LOW
                     (SEG-VISIBLEI 1
                                   (MV-NTH 1
                                           (WM08 (CAR (CAR ADDR-BYTES))
                                                 (CDR (CAR ADDR-BYTES))
                                                 X86)))
                     2 0))))
    :TOP :BASH :BASH
    :BASH :BASH :BASH (:CHANGE-GOAL NIL T)
    :BASH (:DV 2 1)
    (:REWRITE
     GATHER-ALL-PAGING-STRUCTURE-QWORD-ADDRESSES-WITH-XLATE-EQUIV-STRUCTURES)
    :TOP :BASH
    :BASH :BASH)))

(local
 (DEFTHMd RM08-AND-WB-MEMBER-LEMMA-VALUE-HELPER
   (IMPLIES
    (AND
     (CONSP ADDR-BYTES)
     (EQUAL
      (MV-NTH 1
              (IA32E-ENTRIES-FOUND-LA-TO-PA INDEX R-W-X
                                            (LOGHEAD 2 (XR :SEG-VISIBLE 1 X86))
                                            X86))
      (MV-NTH
       1
       (IA32E-ENTRIES-FOUND-LA-TO-PA (CAR (STRIP-CARS ADDR-BYTES))
                                     :W (LOGHEAD 2 (XR :SEG-VISIBLE 1 X86))
                                     X86)))
     (PAGING-ENTRIES-FOUND-P INDEX X86)
     (ALL-PAGING-ENTRIES-FOUND-P (STRIP-CARS ADDR-BYTES)
                                 X86)
     (CONSP (STRIP-CARS ADDR-BYTES))
     (NO-DUPLICATES-P
      (TRANSLATE-ALL-L-ADDRS (STRIP-CARS ADDR-BYTES)
                             :W (LOGHEAD 2 (XR :SEG-VISIBLE 1 X86))
                             X86))
     (NO-DUPLICATES-P (STRIP-CARS ADDR-BYTES))
     (MAPPED-LIN-ADDRS-DISJOINT-FROM-PAGING-STRUCTURE-ADDRS-P
      (STRIP-CARS ADDR-BYTES)
      :W (LOGHEAD 2 (XR :SEG-VISIBLE 1 X86))
      X86)
     (NOT
      (MV-NTH 0
              (IA32E-ENTRIES-FOUND-LA-TO-PA INDEX R-W-X
                                            (LOGHEAD 2 (XR :SEG-VISIBLE 1 X86))
                                            X86)))
     (NO-PAGE-FAULTS-DURING-TRANSLATION-P
      (STRIP-CARS ADDR-BYTES)
      :W (LOGHEAD 2 (XR :SEG-VISIBLE 1 X86))
      X86)
     (EQUAL (LEN (STRIP-CARS ADDR-BYTES))
            (LEN (STRIP-CDRS ADDR-BYTES)))
     (ADDR-BYTE-ALISTP ADDR-BYTES))
    (EQUAL
     (MV-NTH 1
             (RM08 INDEX
                   R-W-X (MV-NTH 1 (WB ADDR-BYTES X86))))
     (NTH
      (POS
       (MV-NTH
        1
        (IA32E-ENTRIES-FOUND-LA-TO-PA (CAR (STRIP-CARS ADDR-BYTES))
                                      :W (LOGHEAD 2 (XR :SEG-VISIBLE 1 X86))
                                      X86))
       (TRANSLATE-ALL-L-ADDRS (STRIP-CARS ADDR-BYTES)
                              :W (LOGHEAD 2 (XR :SEG-VISIBLE 1 X86))
                              X86))
      (STRIP-CDRS ADDR-BYTES))))
   :INSTRUCTIONS
   ((:DV 2 1 2 3 2)
    :X :TOP
    (:IN-THEORY
     (E/D (NO-PAGE-FAULTS-DURING-TRANSLATION-P
           MAPPED-LIN-ADDRS-DISJOINT-FROM-PAGING-STRUCTURE-ADDRS-P
           ALL-PAGING-ENTRIES-FOUND-P
           POS RM08-WM08-EQUAL-IN-SYSTEM-LEVEL-MODE
           DISJOINT-P)
          NIL))
    :BASH (:DV 1)
    (:REWRITE RM08-AND-WB-DISJOINT-LEMMA
              ((CPL (BITOPS::PART-SELECT-WIDTH-LOW
                     (SEG-VISIBLEI 1
                                   (MV-NTH 1
                                           (WM08 (CAR (CAR ADDR-BYTES))
                                                 (CDR (CAR ADDR-BYTES))
                                                 X86)))
                     2 0))))
    :TOP
    :BASH :BASH
    :BASH :BASH
    :BASH
    (:USE
     (:INSTANCE
      GATHER-ALL-PAGING-STRUCTURE-QWORD-ADDRESSES-WITH-XLATE-EQUIV-STRUCTURES
      (X86 X86)
      (X86-EQUIV (MV-NTH 1
                         (WM08 (CAR (CAR ADDR-BYTES))
                               (CDR (CAR ADDR-BYTES))
                               X86)))))
    :BASH :BASH)))

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
                 (no-duplicates-p
                  ;; All linear addresses being written to are unique.
                  (strip-cars addr-bytes))
                 (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                  ;; The write isn't being done to the page tables.
                  (strip-cars addr-bytes) :w cpl (double-rewrite x86))
                 ;; Can I not remove the following hyp?
                 (not (mv-nth 0 (ia32e-entries-found-la-to-pa index r-w-x cpl x86)))
                 (no-page-faults-during-translation-p
                  ;; If the write doesn't succeed, the read can't read
                  ;; what was written, duh.
                  (strip-cars addr-bytes) :w cpl (double-rewrite x86))
                 (equal (len (strip-cars addr-bytes)) (len (strip-cdrs addr-bytes)))
                 (addr-byte-alistp addr-bytes))
            (and
             (equal (mv-nth 0 (rm08 index r-w-x (mv-nth 1 (wb addr-bytes x86))))
                    nil)
             (equal (mv-nth 1 (rm08 index r-w-x (mv-nth 1 (wb addr-bytes x86))))
                    (nth
                     (pos
                      (mv-nth 1 (ia32e-entries-found-la-to-pa index r-w-x cpl x86))
                      (translate-all-l-addrs (strip-cars addr-bytes) :w cpl (double-rewrite x86)))
                     (strip-cdrs addr-bytes)))))
   :hints (("Goal"
            :induct (rm08-and-wb-member-lemma-ind-hint index addr-bytes r-w-x cpl x86)
            :in-theory (e/d* (wb
                              rm08-wm08-disjoint-in-system-level-mode
                              rm08-wm08-equal-in-system-level-mode
                              all-paging-entries-found-p
                              no-page-faults-during-translation-p
                              mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                              member-p
                              rm08-and-wb-member-lemma-error-helper
                              rm08-and-wb-member-lemma-value-helper)
                             ())))))

;; (local
;;  (defthm nth-pos-1-and-cdr-and-minus
;;    (implies (and (not (equal e (car x)))
;;                  (member-p e x)
;;                  (natp n))
;;             (equal (nth (- (pos-1 e x n) n) y)
;;                    (nth (- (pos-1 e (cdr x) n) n) (cdr y))))))

;; (local
;;  (defthm assoc-equal-and-nth-pos-1
;;    (implies (and (equal (len l-addrs) (len bytes))
;;                  (member-p e l-addrs)
;;                  (natp n))
;;             (equal (cdr (assoc-equal e (create-addr-bytes-alist l-addrs bytes)))
;;                    (nth (- (pos-1 e l-addrs n) n) bytes)))
;;    :hints (("Goal"
;;             :induct (create-addr-bytes-alist l-addrs bytes)
;;             :in-theory (e/d* () (nth-pos-1-and-cdr-and-minus)))
;;            ("Subgoal *1/2"
;;             :in-theory (e/d* () (nth-pos-1-and-cdr-and-minus))
;;             :use ((:instance nth-pos-1-and-cdr-and-minus
;;                              (e e)
;;                              (x l-addrs)
;;                              (y bytes)
;;                              (n n)))))))

;; (defthm assoc-equal-and-nth-pos
;;   (implies (and (equal (len l-addrs) (len bytes))
;;                 (member-p e l-addrs))
;;            (equal (cdr (assoc-equal e (create-addr-bytes-alist l-addrs bytes)))
;;                   (nth (pos e l-addrs) bytes)))
;;   :hints (("Goal" :in-theory (e/d* (pos) (assoc-equal-and-nth-pos-1))
;;            :use ((:instance assoc-equal-and-nth-pos-1
;;                             (n 0))))))

;; (defthm len-of-strip-cdrs
;;   (equal (len (strip-cdrs as)) (len as)))

;; (defthm len-of-strip-cars
;;   (equal (len (strip-cars as)) (len as)))

(local
 (DEFTHMD rb-1-wb-subset-in-system-level-mode-helper
   (IMPLIES
    (AND
     (CONSP L-ADDRS-1)
     (EQUAL
      (MV-NTH 1
              (RB-1 (CDR L-ADDRS-1)
                    R-W-X
                    (MV-NTH 1
                            (WB ADDR-BYTES
                                (MV-NTH 2 (RM08 (CAR L-ADDRS-1) R-W-X X86))))
                    NIL))
      (ASSOC-LIST
       (TRANSLATE-ALL-L-ADDRS (CDR L-ADDRS-1)
                              R-W-X
                              (LOGHEAD 2 (XR :SEG-VISIBLE 1 X86))
                              X86)
       (CREATE-ADDR-BYTES-ALIST
        (TRANSLATE-ALL-L-ADDRS (STRIP-CARS ADDR-BYTES)
                               :W (LOGHEAD 2 (XR :SEG-VISIBLE 1 X86))
                               X86)
        (STRIP-CDRS ADDR-BYTES))))
     (PAGING-ENTRIES-FOUND-P (CAR L-ADDRS-1)
                             X86)
     (ALL-PAGING-ENTRIES-FOUND-P (CDR L-ADDRS-1)
                                 X86)
     (ALL-PAGING-ENTRIES-FOUND-P (STRIP-CARS ADDR-BYTES)
                                 X86)
     (MEMBER-P
      (MV-NTH 1
              (IA32E-ENTRIES-FOUND-LA-TO-PA (CAR L-ADDRS-1)
                                            R-W-X
                                            (LOGHEAD 2 (XR :SEG-VISIBLE 1 X86))
                                            X86))
      (TRANSLATE-ALL-L-ADDRS (STRIP-CARS ADDR-BYTES)
                             :W (LOGHEAD 2 (XR :SEG-VISIBLE 1 X86))
                             X86))
     (SUBSET-P (TRANSLATE-ALL-L-ADDRS (CDR L-ADDRS-1)
                                      R-W-X
                                      (LOGHEAD 2 (XR :SEG-VISIBLE 1 X86))
                                      X86)
               (TRANSLATE-ALL-L-ADDRS (STRIP-CARS ADDR-BYTES)
                                      :W (LOGHEAD 2 (XR :SEG-VISIBLE 1 X86))
                                      X86))
     (NO-DUPLICATES-P
      (TRANSLATE-ALL-L-ADDRS (STRIP-CARS ADDR-BYTES)
                             :W (LOGHEAD 2 (XR :SEG-VISIBLE 1 X86))
                             X86))
     (NO-DUPLICATES-P (STRIP-CARS ADDR-BYTES))
     (MAPPED-LIN-ADDRS-DISJOINT-FROM-PAGING-STRUCTURE-ADDRS-P
      (STRIP-CARS ADDR-BYTES)
      :W (LOGHEAD 2 (XR :SEG-VISIBLE 1 X86))
      X86)
     (PAIRWISE-DISJOINT-P-AUX
      (LIST
       (MV-NTH
        1
        (IA32E-ENTRIES-FOUND-LA-TO-PA (CAR L-ADDRS-1)
                                      R-W-X
                                      (LOGHEAD 2 (XR :SEG-VISIBLE 1 X86))
                                      X86)))
      (OPEN-QWORD-PADDR-LIST-LIST
       (GATHER-ALL-PAGING-STRUCTURE-QWORD-ADDRESSES X86)))
     (MAPPED-LIN-ADDRS-DISJOINT-FROM-PAGING-STRUCTURE-ADDRS-P
      (CDR L-ADDRS-1)
      R-W-X
      (LOGHEAD 2 (XR :SEG-VISIBLE 1 X86))
      X86)
     (NOT
      (MV-NTH 0
              (IA32E-ENTRIES-FOUND-LA-TO-PA (CAR L-ADDRS-1)
                                            R-W-X
                                            (LOGHEAD 2 (XR :SEG-VISIBLE 1 X86))
                                            X86)))
     (NO-PAGE-FAULTS-DURING-TRANSLATION-P (CDR L-ADDRS-1)
                                          R-W-X
                                          (LOGHEAD 2 (XR :SEG-VISIBLE 1 X86))
                                          X86)
     (NO-PAGE-FAULTS-DURING-TRANSLATION-P
      (STRIP-CARS ADDR-BYTES)
      :W (LOGHEAD 2 (XR :SEG-VISIBLE 1 X86))
      X86)
     (ADDR-BYTE-ALISTP ADDR-BYTES)
     (TRUE-LISTP ACC))
    (EQUAL
     (MV-NTH 1
             (RB-1 L-ADDRS-1
                   R-W-X (MV-NTH 1 (WB ADDR-BYTES X86))
                   NIL))
     (CONS
      (NTH
       (POS
        (MV-NTH
         1
         (IA32E-ENTRIES-FOUND-LA-TO-PA (CAR L-ADDRS-1)
                                       R-W-X
                                       (LOGHEAD 2 (XR :SEG-VISIBLE 1 X86))
                                       X86))
        (TRANSLATE-ALL-L-ADDRS (STRIP-CARS ADDR-BYTES)
                               :W (LOGHEAD 2 (XR :SEG-VISIBLE 1 X86))
                               X86))
       (STRIP-CDRS ADDR-BYTES))
      (MV-NTH 1
              (RB-1 (CDR L-ADDRS-1)
                    R-W-X
                    (MV-NTH 1
                            (WB ADDR-BYTES
                                (MV-NTH 2 (RM08 (CAR L-ADDRS-1) R-W-X X86))))
                    NIL)))))
   :INSTRUCTIONS
   ((:DV 2 1 2)
    :X :TOP
    (:IN-THEORY
     (E/D (NO-PAGE-FAULTS-DURING-TRANSLATION-P
           MAPPED-LIN-ADDRS-DISJOINT-FROM-PAGING-STRUCTURE-ADDRS-P
           ALL-PAGING-ENTRIES-FOUND-P)
          NIL))
    :BASH
    (:IN-THEORY (E/D NIL
                     (MV-NTH-1-WB-AND-XLATE-EQUIV-X86S-DISJOINT)))
    (:USE (:INSTANCE MV-NTH-1-WB-AND-XLATE-EQUIV-X86S-DISJOINT
                     (X86-1 (MV-NTH 2 (RM08 (CAR L-ADDRS-1) R-W-X X86)))
                     (X86-2 X86)
                     (ADDR-BYTES ADDR-BYTES)))
    (:USE
     (:INSTANCE
      MV-NTH-1-RB-1-AND-XLATE-EQUIV-X86S-DISJOINT
      (X86-1 (MV-NTH 1
                     (WB ADDR-BYTES
                         (MV-NTH 2 (RM08 (CAR L-ADDRS-1) R-W-X X86)))))
      (X86-2 (MV-NTH 1 (WB ADDR-BYTES X86)))
      (L-ADDRS (CDR L-ADDRS-1))
      (R-W-X R-W-X)
      (ACC NIL)))
    :BASH)))

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
                ;; Shouldn't need the following hyp...
                (all-paging-entries-found-p (strip-cars addr-bytes) x86)

                (subset-p
                 ;; The physical addresses corresponding to l-addrs-1
                 ;; are a subset of those corresponding to (strip-cars addr-bytes).
                 (translate-all-l-addrs l-addrs-1 r-w-x cpl x86)
                 (translate-all-l-addrs (strip-cars addr-bytes) :w cpl x86))

                ;; Note that the following two hypotheses about
                ;; uniqueness of linear and physical addresses means
                ;; that I need a "wb-remove-duplicate-writes" kinda
                ;; theorem about wb in the system-level mode.
                (no-duplicates-p
                 ;; All physical addresses being written to are
                 ;; unique.
                 (translate-all-l-addrs (strip-cars addr-bytes) :w cpl (double-rewrite x86)))
                (no-duplicates-p
                 ;; All linear addresses being written to are unique.
                 (strip-cars addr-bytes))

                (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                 ;; The write isn't being done to the page tables.
                 (strip-cars addr-bytes) :w cpl (double-rewrite x86))
                (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                 ;; Shouldn't need the following hyp...
                 l-addrs-1 r-w-x cpl (double-rewrite x86))
                (no-page-faults-during-translation-p l-addrs-1 r-w-x cpl (double-rewrite x86))
                ;; Shouldn't need the following hyp...
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
                (all-paging-entries-found-p l-addrs-1 x86)
                ;; Shouldn't need the following hyp...
                (all-paging-entries-found-p (strip-cars addr-bytes) x86)

                (subset-p
                 ;; The physical addresses corresponding to l-addrs-1
                 ;; are a subset of those corresponding to (strip-cars addr-bytes).
                 (translate-all-l-addrs l-addrs-1 r-w-x cpl x86)
                 (translate-all-l-addrs (strip-cars addr-bytes) :w cpl x86))

                ;; Note that the following two hypotheses about
                ;; uniqueness of linear and physical addresses means
                ;; that I need a "wb-remove-duplicate-writes" kinda
                ;; theorem about wb in the system-level mode.
                (no-duplicates-p
                 ;; All physical addresses being written to are
                 ;; unique.
                 (translate-all-l-addrs (strip-cars addr-bytes) :w cpl (double-rewrite x86)))
                (no-duplicates-p
                 ;; All linear addresses being written to are unique.
                 (strip-cars addr-bytes))

                (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                 ;; The write isn't being done to the page tables.
                 (strip-cars addr-bytes) :w cpl (double-rewrite x86))
                (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                 ;; Shouldn't need the following hyp...
                 l-addrs-1 r-w-x cpl (double-rewrite x86))
                (no-page-faults-during-translation-p l-addrs-1 r-w-x cpl (double-rewrite x86))
                ;; Shouldn't need the following hyp...
                (no-page-faults-during-translation-p (strip-cars addr-bytes) :w cpl (double-rewrite x86))
                (addr-byte-alistp addr-bytes))
           (equal (mv-nth 1 (rb l-addrs-1 r-w-x (mv-nth 1 (wb addr-bytes x86))))
                  (assoc-list
                   (translate-all-l-addrs l-addrs-1 r-w-x cpl x86)
                   (create-addr-bytes-alist
                    (translate-all-l-addrs (strip-cars addr-bytes) :w cpl x86)
                    (strip-cdrs addr-bytes)))))
  :hints (("Goal" :in-theory (e/d* (rb rb-1-wb-subset-in-system-level-mode)
                                   (rb-1 signed-byte-p unsigned-byte-p
                                         force (force))))))

;; ======================================================================
