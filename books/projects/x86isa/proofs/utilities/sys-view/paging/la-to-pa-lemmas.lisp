;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")
(include-book "pml4-table-lemmas" :ttags :all)
(include-book "gather-paging-structures-thms" :ttags :all)

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))

(local (in-theory (e/d () (unsigned-byte-p signed-byte-p))))

;; ======================================================================

(defthm xlate-equiv-memory-and-cr0-cong
  (implies (xlate-equiv-memory x86-1 x86-2)
           (equal (bool->bit (logbitp 16 (xr :ctr *cr0* x86-1)))
                  (bool->bit (logbitp 16 (xr :ctr *cr0* x86-2)))))
  :hints (("Goal" :in-theory (e/d* (xlate-equiv-memory xlate-equiv-structures)
                                   ())))
  :rule-classes :congruence)

(defthm xlate-equiv-memory-and-cr3-cong
  (implies (xlate-equiv-memory x86-1 x86-2)
           (equal (loghead 40 (logtail 12 (xr :ctr *cr3* x86-1)))
                  (loghead 40 (logtail 12 (xr :ctr *cr3* x86-2)))))
  :hints (("Goal" :in-theory (e/d* (xlate-equiv-memory xlate-equiv-structures)
                                   ())))
  :rule-classes :congruence)

(defthm xlate-equiv-memory-and-cr4-cong
  (implies (xlate-equiv-memory x86-1 x86-2)
           (equal (bool->bit (logbitp 20 (xr :ctr *cr4* x86-1)))
                  (bool->bit (logbitp 20 (xr :ctr *cr4* x86-2)))))
  :hints (("Goal" :in-theory (e/d* (xlate-equiv-memory xlate-equiv-structures)
                                   ())))
  :rule-classes :congruence)

(defthm xlate-equiv-memory-and-msr-cong
  (implies (xlate-equiv-memory x86-1 x86-2)
           (equal (bool->bit (logbitp 11 (xr :msr *ia32_efer-idx* x86-1)))
                  (bool->bit (logbitp 11 (xr :msr *ia32_efer-idx* x86-2)))))
  :hints (("Goal" :in-theory (e/d* (xlate-equiv-memory xlate-equiv-structures)
                                   ())))
  :rule-classes :congruence)

(defthm xlate-equiv-memory-and-rflags-cong
  (implies (xlate-equiv-memory x86-1 x86-2)
           (equal (bool->bit (logbitp 18 (xr :rflags 0 x86-1)))
                  (bool->bit (logbitp 18 (xr :rflags 0 x86-2)))))
  :hints (("Goal" :in-theory (e/d* (xlate-equiv-memory xlate-equiv-structures)
                                   ())))
  :rule-classes :congruence)

(defthm xlate-equiv-memory-and-seg-visible-cong
  (implies (xlate-equiv-memory x86-1 x86-2)
           (equal (loghead 2 (xr :seg-visible 1 x86-1))
                  (loghead 2 (xr :seg-visible 1 x86-2))))
  :hints (("Goal" :in-theory (e/d* (xlate-equiv-memory xlate-equiv-structures)
                                   ())))
  :rule-classes :congruence)

(defthm xlate-equiv-memory-and-marking-view-cong
  (implies (xlate-equiv-memory x86-1 x86-2)
           (equal (xr :marking-view 0 x86-1)
                  (xr :marking-view 0 x86-2)))
  :hints (("Goal" :in-theory (e/d* (xlate-equiv-memory xlate-equiv-structures)
                                   ())))
  :rule-classes :congruence)

(defthm xlate-equiv-memory-and-app-view-cong
  (implies (xlate-equiv-memory x86-1 x86-2)
           (equal (xr :app-view 0 x86-1)
                  (xr :app-view 0 x86-2)))
  :hints (("Goal" :in-theory (e/d* (xlate-equiv-memory xlate-equiv-structures)
                                   ())))
  :rule-classes :congruence)

(defthm xlate-equiv-memory-in-app-view-implies-equal-states
  (implies (and (xlate-equiv-memory x86-1 x86-2)
                (app-view x86-1))
           (equal x86-1 x86-2))
  :hints (("Goal" :in-theory (e/d* (xlate-equiv-memory) ())))
  :rule-classes nil)

;; ======================================================================

;; Lemmas about ia32e-la-to-pa:

(defthm ia32e-la-to-pa-in-app-view
  (implies (app-view x86)
           (equal (ia32e-la-to-pa lin-addr r-w-x x86)
                  (mv t 0 x86)))
  :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa) ()))))

(defthmd xlate-equiv-memory-and-ia32e-la-to-pa
  (implies (xlate-equiv-memory (double-rewrite x86-1) x86-2)
           (and
            (equal (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x x86-1))
                   (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x x86-2)))
            (equal (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x x86-1))
                   (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x x86-2)))))
  :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa) ()))))

(defthm xlate-equiv-memory-and-mv-nth-0-ia32e-la-to-pa-cong
  (implies (xlate-equiv-memory x86-1 x86-2)
           (equal (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x x86-1))
                  (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x x86-2))))
  :hints (("Goal" :use ((:instance xlate-equiv-memory-and-ia32e-la-to-pa))))
  :rule-classes :congruence)

(defthm xlate-equiv-memory-and-mv-nth-1-ia32e-la-to-pa-cong
  (implies (xlate-equiv-memory x86-1 x86-2)
           (equal (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x x86-1))
                  (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x x86-2))))
  :hints (("Goal" :use ((:instance xlate-equiv-memory-and-ia32e-la-to-pa))))
  :rule-classes :congruence)

(defthm xlate-equiv-structures-and-mv-nth-2-ia32e-la-to-pa
  (xlate-equiv-structures (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x x86))
                          (double-rewrite x86))
  :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa) (force (force))))))

(defthm xlate-equiv-structures-and-two-mv-nth-2-ia32e-la-to-pa-cong
  (implies (xlate-equiv-structures x86-1 x86-2)
           (xlate-equiv-structures (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x x86-1))
                                   (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x x86-2))))
  :rule-classes :congruence)

(local
 (encapsulate
   ()

   (local (in-theory (e/d* ()
                           (loghead-of-non-integerp
                            (:t ctri-is-n64p)
                            acl2::ash-0
                            (:t bitops::logtail-natp)
                            unsigned-byte-p-of-logtail))))

   (defthm all-mem-except-paging-structures-equal-with-mv-nth-2-ia32e-la-to-pa-1G-pages
     (implies
      (and
       ;; (equal (page-present
       ;;         (rm-low-64 (pml4-table-entry-addr (logext 48 lin-addr) (pml4-table-base-addr x86)) x86))
       ;;        1)
       (equal
        (page-size (rm-low-64
                    (pml4-table-entry-addr (logext 48 lin-addr) (pml4-table-base-addr x86)) x86))
        0)
       (equal
        (page-size
         (rm-low-64 (page-dir-ptr-table-entry-addr (logext 48 lin-addr) (page-dir-ptr-table-base-addr (logext 48 lin-addr) x86))
                    x86))
        1))
      (all-mem-except-paging-structures-equal
       (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x x86))
       x86))
     :hints (("Goal"

              :in-theory (e/d* (ia32e-la-to-pa
                                ia32e-la-to-pa-pml4-table
                                ia32e-la-to-pa-page-dir-ptr-table)
                               (bitops::logand-with-negated-bitmask
                                accessed-bit
                                dirty-bit
                                force (force)
                                not)))))

   (defthm all-mem-except-paging-structures-equal-with-mv-nth-2-ia32e-la-to-pa-2M-and-4K-pages
     (implies
      (and
       ;; (equal
       ;;  (page-present
       ;;   (rm-low-64 (pml4-table-entry-addr (logext 48 lin-addr) (pml4-table-base-addr x86)) x86))
       ;;  1)
       (equal
        (page-size
         (rm-low-64 (pml4-table-entry-addr (logext 48 lin-addr) (pml4-table-base-addr x86)) x86))
        0)
       ;; (equal
       ;;  (page-present
       ;;   (rm-low-64 (page-dir-ptr-table-entry-addr (logext 48 lin-addr) (page-dir-ptr-table-base-addr (logext 48 lin-addr) x86)) x86))
       ;;  1)
       ;; (equal
       ;;  (page-present
       ;;   (rm-low-64 (page-directory-entry-addr (logext 48 lin-addr) (page-directory-base-addr (logext 48 lin-addr) x86)) x86))
       ;;  1)
       )
      (all-mem-except-paging-structures-equal
       (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x x86))
       x86))
     :hints (("Goal"

              :in-theory (e/d* (ia32e-la-to-pa
                                ia32e-la-to-pa-pml4-table
                                ia32e-la-to-pa-page-dir-ptr-table)
                               (bitops::logand-with-negated-bitmask
                                accessed-bit
                                dirty-bit
                                force (force)
                                not)))))

   ;; (defthm all-mem-except-paging-structures-equal-with-mv-nth-2-ia32e-la-to-pa-pml4-page-not-present
   ;;   (implies
   ;;    (equal (page-present
   ;;            (rm-low-64 (pml4-table-entry-addr (logext 48 lin-addr) (pml4-table-base-addr x86)) x86))
   ;;           0)
   ;;    (all-mem-except-paging-structures-equal
   ;;     (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x x86))
   ;;     x86))
   ;;   :hints (("Goal"

   ;;            :in-theory (e/d* (ia32e-la-to-pa
   ;;                              ia32e-la-to-pa-pml4-table)
   ;;                             (bitops::logand-with-negated-bitmask
   ;;                              accessed-bit
   ;;                              dirty-bit
   ;;                              force (force)
   ;;                              not)))))

   (defthm all-mem-except-paging-structures-equal-with-mv-nth-2-ia32e-la-to-pa-pml4-page-size=1
     (implies
      (equal (page-size
              (rm-low-64 (pml4-table-entry-addr (logext 48 lin-addr) (pml4-table-base-addr x86)) x86))
             1)
      (all-mem-except-paging-structures-equal
       (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x x86))
       x86))
     :hints (("Goal"

              :in-theory (e/d* (ia32e-la-to-pa
                                ia32e-la-to-pa-pml4-table
                                paging-entry-no-page-fault-p
                                page-fault-exception)
                               (bitops::logand-with-negated-bitmask
                                accessed-bit
                                dirty-bit
                                force (force)
                                not)))))

   ;; (defthm all-mem-except-paging-structures-equal-with-mv-nth-2-ia32e-la-to-pa-page-dir-ptr-table-page-not-present
   ;;   (implies
   ;;    (and
   ;;     (equal
   ;;      (page-size
   ;;       (rm-low-64 (page-dir-ptr-table-entry-addr (logext 48 lin-addr) (page-dir-ptr-table-base-addr (logext 48 lin-addr) x86)) x86))
   ;;      0)
   ;;     ;; (equal
   ;;     ;;  (page-present
   ;;     ;;   (rm-low-64 (page-dir-ptr-table-entry-addr (logext 48 lin-addr) (page-dir-ptr-table-base-addr (logext 48 lin-addr) x86)) x86))
   ;;     ;;  0)
   ;;     )
   ;;    (all-mem-except-paging-structures-equal
   ;;     (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x x86))
   ;;     x86))
   ;;   :hints (("Goal"

   ;;            :in-theory (e/d* (ia32e-la-to-pa
   ;;                              ia32e-la-to-pa-pml4-table
   ;;                              ia32e-la-to-pa-page-dir-ptr-table)
   ;;                             (bitops::logand-with-negated-bitmask
   ;;                              accessed-bit
   ;;                              dirty-bit
   ;;                              force (force)
   ;;                              not)))))

   ;; (defthm all-mem-except-paging-structures-equal-with-mv-nth-2-ia32e-la-to-pa-pdpte-ps=0-and-pd-pp=0
   ;;   (implies
   ;;    (and
   ;;     (equal
   ;;      (page-size
   ;;       (rm-low-64 (page-dir-ptr-table-entry-addr (logext 48 lin-addr) (page-dir-ptr-table-base-addr (logext 48 lin-addr) x86)) x86))
   ;;      0)
   ;;     ;; (equal
   ;;     ;;  (page-present
   ;;     ;;   (rm-low-64 (page-directory-entry-addr (logext 48 lin-addr) (page-directory-base-addr (logext 48 lin-addr) x86)) x86))
   ;;     ;;  0)
   ;;     )
   ;;    (all-mem-except-paging-structures-equal
   ;;     (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x x86))
   ;;     x86))
   ;;   :hints (("Goal"

   ;;            :in-theory (e/d* (ia32e-la-to-pa
   ;;                              ia32e-la-to-pa-pml4-table
   ;;                              ia32e-la-to-pa-page-dir-ptr-table
   ;;                              ia32e-la-to-pa-page-directory)
   ;;                             (bitops::logand-with-negated-bitmask
   ;;                              accessed-bit
   ;;                              dirty-bit
   ;;                              force (force)
   ;;                              not)))))
   ))

(defthm all-mem-except-paging-structures-equal-with-mv-nth-2-ia32e-la-to-pa
  (all-mem-except-paging-structures-equal
   (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x x86))
   (double-rewrite x86))
  :hints (("Goal"
           :cases ((and
                    ;; (equal (page-present
                    ;;         (rm-low-64 (pml4-table-entry-addr (logext 48 lin-addr) (pml4-table-base-addr x86)) x86))
                    ;;        1)
                    (equal
                     (page-size (rm-low-64
                                 (pml4-table-entry-addr (logext 48 lin-addr) (pml4-table-base-addr x86)) x86))
                     0)
                    (equal
                     (page-size
                      (rm-low-64 (page-dir-ptr-table-entry-addr (logext 48 lin-addr) (page-dir-ptr-table-base-addr (logext 48 lin-addr) x86))
                                 x86))
                     1))

                   (and
                    ;; (equal
                    ;;  (page-present
                    ;;   (rm-low-64 (pml4-table-entry-addr (logext 48 lin-addr) (pml4-table-base-addr x86)) x86))
                    ;;  1)
                    (equal
                     (page-size
                      (rm-low-64 (pml4-table-entry-addr (logext 48 lin-addr) (pml4-table-base-addr x86)) x86))
                     0)
                    ;; (equal
                    ;;  (page-present
                    ;;   (rm-low-64 (page-dir-ptr-table-entry-addr (logext 48 lin-addr) (page-dir-ptr-table-base-addr (logext 48 lin-addr) x86)) x86))
                    ;;  1)
                    ;; (equal
                    ;;  (page-present
                    ;;   (rm-low-64 (page-directory-entry-addr (logext 48 lin-addr) (page-directory-base-addr (logext 48 lin-addr) x86)) x86))
                    ;;  1)
                    ))
           :in-theory (e/d* ()
                            (bitops::logand-with-negated-bitmask
                             accessed-bit
                             dirty-bit
                             force (force)
                             not)))))

(defthm all-mem-except-paging-structures-equal-with-two-mv-nth-2-ia32e-la-to-pa-cong
  (implies (all-mem-except-paging-structures-equal x86-1 x86-2)
           (all-mem-except-paging-structures-equal
            (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x x86-1))
            (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x x86-2))))
  :rule-classes :congruence)

(defthm xlate-equiv-memory-with-mv-nth-2-ia32e-la-to-pa
  ;; without the 64-bit mode hyp, this theorem is not true,
  ;; because ia32e-la-to-pa may mark bits in the state
  (implies (64-bit-modep x86)
           (xlate-equiv-memory
            (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x x86))
            (double-rewrite x86)))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (e/d* (xlate-equiv-memory)
                            (bitops::logand-with-negated-bitmask
                             accessed-bit
                             dirty-bit
                             not)))))

(defthm xlate-equiv-memory-with-two-mv-nth-2-ia32e-la-to-pa-cong
  (implies (xlate-equiv-memory x86-1 x86-2)
           (xlate-equiv-memory
            (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x x86-1))
            (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x x86-2))))
  :rule-classes :congruence
  ;; add the following after adding 64-bit mode hyp to previous theorem:
  :hints (("Goal" :in-theory (enable xlate-equiv-memory))))

(defthm two-page-walks-ia32e-la-to-pa
  (implies
   ;; the 64-bit mode hyp makes the proof of this theorem easy
   ;; (via xlate-equiv-memory-with-mv-nth-2-ia32e-la-to-pa above),
   ;; but could this hyp be removed from here?
   (64-bit-modep x86)
   (and

    (equal
     (mv-nth 0 (ia32e-la-to-pa lin-addr-1 r-w-x-1
                               (mv-nth 2 (ia32e-la-to-pa lin-addr-2 r-w-x-2 x86))))
     (mv-nth 0 (ia32e-la-to-pa lin-addr-1 r-w-x-1 x86)))

    (equal
     (mv-nth 1 (ia32e-la-to-pa lin-addr-1 r-w-x-1
                               (mv-nth 2 (ia32e-la-to-pa lin-addr-2 r-w-x-2 x86))))
     (mv-nth 1 (ia32e-la-to-pa lin-addr-1 r-w-x-1 x86)))))

  :hints (("Goal" :in-theory (e/d* () (ia32e-la-to-pa)))))

(in-theory (e/d* () (ia32e-la-to-pa)))

;; ======================================================================

(defthm gather-all-paging-structure-qword-addresses-mv-nth-2-ia32e-la-to-pa
  (equal (gather-all-paging-structure-qword-addresses
          (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x x86)))
         (gather-all-paging-structure-qword-addresses x86))
  :hints (("Goal"
           :use ((:instance
                  gather-all-paging-structure-qword-addresses-with-xlate-equiv-structures
                  (x86-equiv (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x x86))))))))


(defthm xlate-equiv-entries-at-qword-addresses-mv-nth-2-ia32e-la-to-pa
  (implies (equal addrs (gather-all-paging-structure-qword-addresses x86))
           (equal (xlate-equiv-entries-at-qword-addresses
                   addrs addrs
                   x86
                   (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x x86)))
                  (xlate-equiv-entries-at-qword-addresses addrs addrs x86 x86)))
  :hints (("Goal" :in-theory (e/d* ()
                                   (xlate-equiv-structures-and-xlate-equiv-entries-at-qword-addresses
                                    booleanp-of-xlate-equiv-entries-at-qword-addresses))
           :use ((:instance xlate-equiv-structures-and-xlate-equiv-entries-at-qword-addresses
                            (addrs (gather-all-paging-structure-qword-addresses x86))
                            (x86 x86)
                            (x86-equiv (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x x86))))
                 (:instance booleanp-of-xlate-equiv-entries-at-qword-addresses
                            (addrs (gather-all-paging-structure-qword-addresses x86))
                            (x x86)
                            (y x86))
                 (:instance booleanp-of-xlate-equiv-entries-at-qword-addresses
                            (addrs (gather-all-paging-structure-qword-addresses x86))
                            (x x86)
                            (y (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x x86))))))))

;; ======================================================================

;; Lemmas about las-to-pas:

(defthmd xlate-equiv-memory-and-las-to-pas
  (implies (xlate-equiv-memory (double-rewrite x86-1) x86-2)
           (and
            (equal (mv-nth 0 (las-to-pas n lin-addr r-w-x x86-1))
                   (mv-nth 0 (las-to-pas n lin-addr r-w-x x86-2)))
            (equal (mv-nth 1 (las-to-pas n lin-addr r-w-x x86-1))
                   (mv-nth 1 (las-to-pas n lin-addr r-w-x x86-2)))))
  :hints (("Goal"
           :induct (cons (las-to-pas n lin-addr r-w-x x86-1)
                         (las-to-pas n lin-addr r-w-x x86-2)))))

(defthm xlate-equiv-memory-and-mv-nth-0-las-to-pas-cong
  (implies (xlate-equiv-memory x86-1 x86-2)
           (equal (mv-nth 0 (las-to-pas n lin-addr r-w-x x86-1))
                  (mv-nth 0 (las-to-pas n lin-addr r-w-x x86-2))))
  :hints (("Goal" :in-theory (e/d* (xlate-equiv-memory-and-las-to-pas) ())))
  :rule-classes :congruence)

(defthm xlate-equiv-memory-and-mv-nth-1-las-to-pas-cong
  (implies (xlate-equiv-memory x86-1 x86-2)
           (equal (mv-nth 1 (las-to-pas n lin-addr r-w-x x86-1))
                  (mv-nth 1 (las-to-pas n lin-addr r-w-x x86-2))))
  :hints (("Goal" :in-theory (e/d* (xlate-equiv-memory-and-las-to-pas) ())))
  :rule-classes :congruence)

(defthm xlate-equiv-memory-with-mv-nth-2-las-to-pas
  ;; the 64-bit mode hyp makes the proof of this theorem easy
  ;; (via xlate-equiv-memory-with-mv-nth-2-ia32e-la-to-pa),
  ;; but could this hyp be removed from here?
  (implies (64-bit-modep x86)
           (xlate-equiv-memory
            (mv-nth 2 (las-to-pas n lin-addr r-w-x x86))
            (double-rewrite x86)))
  :hints (("Goal" :induct (las-to-pas n lin-addr r-w-x x86))))

(defthm xlate-equiv-memory-with-two-mv-nth-2-las-to-pas-cong
  (implies (xlate-equiv-memory x86-1 x86-2)
           (xlate-equiv-memory
            (mv-nth 2 (las-to-pas n lin-addr r-w-x x86-1))
            (mv-nth 2 (las-to-pas n lin-addr r-w-x x86-2))))
  :hints (("Goal"
           :induct (cons (las-to-pas n lin-addr r-w-x x86-1)
                         (las-to-pas n lin-addr r-w-x x86-2))))
  :rule-classes :congruence)

;; ======================================================================
