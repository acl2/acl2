;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")
(include-book "gather-paging-structures" :ttags :all)

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))

(local (in-theory (e/d () (unsigned-byte-p signed-byte-p))))

;; ======================================================================

;; Some lemmas about page-table-entry-no-page-fault-p:

(defthm gather-all-paging-structure-qword-addresses-paging-entry-no-page-fault-p
  (equal (gather-all-paging-structure-qword-addresses
          (mv-nth 2 (paging-entry-no-page-fault-p
                     structure-type lin-addr entry
                     u/s-acc r/w-acc x/d-acc
                     wp smep smap ac nxe r-w-x cpl
                     x86 ignored)))
         (gather-all-paging-structure-qword-addresses x86))
  :hints (("Goal" :in-theory (e/d* (paging-entry-no-page-fault-p
                                    page-fault-exception)
                                   ()))))

(defthm xlate-equiv-entries-at-qword-addresses-paging-entry-no-page-fault-p
  (equal
   (xlate-equiv-entries-at-qword-addresses
    addrs addrs x86
    (mv-nth 2 (paging-entry-no-page-fault-p
               structure-type lin-addr entry
               u/s-acc r/w-acc x/d-acc
               wp smep smap ac nxe r-w-x cpl
               x86 ignored)))
   (xlate-equiv-entries-at-qword-addresses addrs addrs x86 x86))
  :hints (("Goal"
           :in-theory (e/d* (xlate-equiv-entries-at-qword-addresses
                             paging-entry-no-page-fault-p
                             page-fault-exception)
                            ()))))

(defthm mv-nth-0-paging-entry-no-page-fault-p-with-xlate-equiv-entries
  ;; See mv-nth-0-paging-entry-no-page-fault-p-and-similar-entries in
  ;; machine/x86-ia32e-paging.lisp: that lemma is essentially the same
  ;; as this one, except that it is not in terms of
  ;; xlate-equiv-entries.
  (implies (xlate-equiv-entries e-1 e-2)
           (equal (mv-nth
                   0
                   (paging-entry-no-page-fault-p
                    structure-type lin-addr e-1
                    u/s-acc r/w-acc x/d-acc
                    wp smep smap ac nxe r-w-x cpl
                    x86 ignored))
                  (mv-nth
                   0
                   (paging-entry-no-page-fault-p
                    structure-type lin-addr e-2
                    u/s-acc r/w-acc x/d-acc
                    wp smep smap ac nxe r-w-x cpl
                    x86 ignored))))
  :hints (("Goal"
           :in-theory (e/d* (paging-entry-no-page-fault-p
                             page-fault-exception)
                            (xlate-equiv-structures
                             bitops::logand-with-negated-bitmask
                             bitops::logior-equal-0
                             not))
           :use ((:instance xlate-equiv-entries-and-page-size
                            (e-1 (loghead 64 e-1))
                            (e-2 (loghead 64 e-2)))
                 (:instance xlate-equiv-entries-and-page-execute-disable
                            (e-1 (loghead 64 e-1))
                            (e-2 (loghead 64 e-2)))
                 (:instance xlate-equiv-entries-and-logtail
                            (e-1 (loghead 64 e-1))
                            (e-2 (loghead 64 e-2))
                            (n 52))
                 (:instance xlate-equiv-entries-and-logtail
                            (e-1 (loghead 64 e-1))
                            (e-2 (loghead 64 e-2))
                            (n 13)))))
  :rule-classes :congruence)

(defthm mv-nth-2-paging-entry-no-page-fault-p-with-xlate-equiv-entries
  (implies (xlate-equiv-entries e-1 e-2)
           (equal (mv-nth 2
                          (paging-entry-no-page-fault-p
                           structure-type lin-addr e-1
                           u/s-acc r/w-acc x/d-acc
                           wp smep smap ac nxe r-w-x cpl
                           x86 ignored))
                  (mv-nth 2
                          (paging-entry-no-page-fault-p
                           structure-type lin-addr e-2
                           u/s-acc r/w-acc x/d-acc
                           wp smep smap ac nxe r-w-x cpl
                           x86 ignored))))
  :hints (("Goal"
           :use ((:instance xlate-equiv-entries-and-page-size
                            (e-1 (loghead 64 e-1))
                            (e-2 (loghead 64 e-2)))
                 (:instance xlate-equiv-entries-and-page-execute-disable
                            (e-1 (loghead 64 e-1))
                            (e-2 (loghead 64 e-2)))
                 (:instance xlate-equiv-entries-and-logtail
                            (e-1 (loghead 64 e-1))
                            (e-2 (loghead 64 e-2))
                            (n 52))
                 (:instance xlate-equiv-entries-and-logtail
                            (e-1 (loghead 64 e-1))
                            (e-2 (loghead 64 e-2))
                            (n 13)))
           :in-theory (e/d* (paging-entry-no-page-fault-p
                             page-fault-exception)
                            (bitops::logand-with-negated-bitmask
                             (:meta acl2::mv-nth-cons-meta)
                             force (force)))))
  :rule-classes :congruence)

(defthm mv-nth-0-paging-entry-no-page-fault-p-with-xlate-equiv-structures
  (implies (xlate-equiv-structures x86-1 x86-2)
           (equal (mv-nth
                   0
                   (paging-entry-no-page-fault-p
                    structure-type lin-addr entry
                    u/s-acc r/w-acc x/d-acc
                    wp smep smap ac nxe r-w-x cpl
                    x86-1 ignored))
                  (mv-nth
                   0
                   (paging-entry-no-page-fault-p
                    structure-type lin-addr entry
                    u/s-acc r/w-acc x/d-acc
                    wp smep smap ac nxe r-w-x cpl
                    x86-2 ignored))))
  :hints (("Goal"
           :in-theory (e/d* (paging-entry-no-page-fault-p
                             page-fault-exception)
                            (bitops::logand-with-negated-bitmask
                             bitops::logior-equal-0
                             not))))
  :rule-classes :congruence)

(defthm mv-nth-2-paging-entry-no-page-fault-p-with-xlate-equiv-structures
  (implies (x86p x86)
           (xlate-equiv-structures
            (mv-nth 2 (paging-entry-no-page-fault-p
                       structure-type lin-addr entry
                       u/s-acc r/w-acc x/d-acc
                       wp smep smap ac nxe r-w-x cpl
                       x86 ignored))
            (double-rewrite x86)))
  :hints (("Goal" :in-theory (e/d* (paging-entry-no-page-fault-p
                                    page-fault-exception
                                    xlate-equiv-structures)
                                   ()))))

;; ======================================================================

;; Defining another equivalence relation: xlate-equiv-memory:

(define xlate-equiv-memory (x86-1 x86-2)
  :non-executable t
  :guard (and (x86p x86-1) (x86p x86-2))
  (and (xlate-equiv-structures x86-1 x86-2)
       (all-mem-except-paging-structures-equal x86-1 x86-2))
  ///
  (defequiv xlate-equiv-memory)

  (defthm xlate-equiv-memory-refines-xlate-equiv-structures
    (implies (xlate-equiv-memory x86-1 x86-2)
             (xlate-equiv-structures x86-1 x86-2))
    :rule-classes :refinement)

  (defthm xlate-equiv-memory-refines-all-mem-except-paging-structures-equal
    (implies (xlate-equiv-memory x86-1 x86-2)
             (all-mem-except-paging-structures-equal x86-1 x86-2))
    :rule-classes :refinement))

(defthm multiple-of-8-disjoint-with-addr-range-and-open-qword-paddr-list-to-member-p
  (implies (and (equal (loghead 3 index) 0)
                (mult-8-qword-paddr-listp addrs)
                (physical-address-p index))
           (equal (disjoint-p (addr-range 8 index) (open-qword-paddr-list addrs))
                  (not (member-p index addrs))))
  :hints (("Goal" :in-theory (e/d* (disjoint-p member-p) ()))))

(defthm xlate-equiv-structures-and-xlate-equiv-entries-rm-low-64-with-page-table-entry-addr
  (implies (and (xlate-equiv-structures x86-1 x86-2)
                (member-p (page-table-entry-addr lin-addr base-addr)
                          (gather-all-paging-structure-qword-addresses x86-1)))
           (xlate-equiv-entries (rm-low-64 (page-table-entry-addr lin-addr base-addr) x86-1)
                                (rm-low-64 (page-table-entry-addr lin-addr base-addr) x86-2)))
  :hints (("Goal" :use ((:instance xlate-equiv-structures-and-xlate-equiv-entries
                                   (index (page-table-entry-addr lin-addr base-addr)))))))

(defthm xlate-equiv-structures-and-logtail-12-rm-low-64-with-page-table-entry-addr
  (implies (and (xlate-equiv-structures x86-1 x86-2)
                (member-p (page-table-entry-addr lin-addr base-addr)
                          (gather-all-paging-structure-qword-addresses x86-1)))
           (equal (logtail 12 (rm-low-64 (page-table-entry-addr lin-addr base-addr) x86-1))
                  (logtail 12 (rm-low-64 (page-table-entry-addr lin-addr base-addr) x86-2))))
  :hints (("Goal" :use ((:instance xlate-equiv-entries-and-logtail
                                   (e-1 (rm-low-64 (page-table-entry-addr lin-addr base-addr) x86-1))
                                   (e-2 (rm-low-64 (page-table-entry-addr lin-addr base-addr) x86-2))
                                   (n 12))))))

(defthm xlate-equiv-memory-and-xlate-equiv-entries-rm-low-64-with-page-table-entry-addr
  ;; (page-table-entry-addr lin-addr base-addr) is either a member of
  ;; gather-all-paging-structure-qword-addresses (because it is a
  ;; quadword-aligned address) or it is a member of the rest of the
  ;; memory (all-mem-except-paging-structures-equal)....
  (implies (xlate-equiv-memory x86-1 x86-2)
           (xlate-equiv-entries (rm-low-64 (page-table-entry-addr lin-addr base-addr) x86-1)
                                (rm-low-64 (page-table-entry-addr lin-addr base-addr) x86-2)))
  :hints (("Goal" :in-theory (e/d* (xlate-equiv-memory) ())
           :cases
           ((not (disjoint-p (addr-range 8 (page-table-entry-addr lin-addr base-addr))
                             (open-qword-paddr-list
                              (gather-all-paging-structure-qword-addresses x86-1)))))))
  :rule-classes :congruence)

(defthm xlate-equiv-memory-and-logtail-12-rm-low-64-with-page-table-entry-addr
  (implies (xlate-equiv-memory x86-1 x86-2)
           (equal (logtail 12 (rm-low-64 (page-table-entry-addr lin-addr base-addr) x86-1))
                  (logtail 12 (rm-low-64 (page-table-entry-addr lin-addr base-addr) x86-2))))
  :hints (("Goal"
           :in-theory (e/d* ()
                            (xlate-equiv-memory-and-xlate-equiv-entries-rm-low-64-with-page-table-entry-addr))
           :use ((:instance xlate-equiv-entries-and-logtail
                            (e-1 (rm-low-64 (page-table-entry-addr lin-addr base-addr) x86-1))
                            (e-2 (rm-low-64 (page-table-entry-addr lin-addr base-addr) x86-2))
                            (n 12))
                 (:instance xlate-equiv-memory-and-xlate-equiv-entries-rm-low-64-with-page-table-entry-addr))))
  :rule-classes :congruence)

;; ======================================================================

;; Finally, lemmas about ia32e-la-to-pa-page-table:

(defthmd xlate-equiv-memory-and-ia32e-la-to-pa-page-table
  (implies (xlate-equiv-memory (double-rewrite x86-1) x86-2)
           (and
            (equal (mv-nth
                    0
                    (ia32e-la-to-pa-page-table
                     lin-addr base-addr u/s-acc r/w-acc x/d-acc
                     wp smep smap ac nxe r-w-x cpl x86-1))
                   (mv-nth
                    0
                    (ia32e-la-to-pa-page-table
                     lin-addr base-addr u/s-acc r/w-acc x/d-acc
                     wp smep smap ac nxe r-w-x cpl x86-2)))
            (equal (mv-nth
                    1
                    (ia32e-la-to-pa-page-table
                     lin-addr base-addr u/s-acc r/w-acc x/d-acc
                     wp smep smap ac nxe r-w-x cpl x86-1))
                   (mv-nth
                    1
                    (ia32e-la-to-pa-page-table
                     lin-addr base-addr u/s-acc r/w-acc x/d-acc
                     wp smep smap ac nxe r-w-x cpl x86-2)))))
  :hints (("Goal"
           :in-theory (e/d* (ia32e-la-to-pa-page-table)
                            (bitops::logand-with-negated-bitmask
                             bitops::logior-equal-0
                             not)))))

(defthm xlate-equiv-memory-and-mv-nth-0-ia32e-la-to-pa-page-table
  (implies (xlate-equiv-memory x86-1 x86-2)
           (equal (mv-nth
                   0
                   (ia32e-la-to-pa-page-table
                    lin-addr base-addr u/s-acc r/w-acc x/d-acc
                    wp smep smap ac nxe r-w-x cpl x86-1))
                  (mv-nth
                   0
                   (ia32e-la-to-pa-page-table
                    lin-addr base-addr u/s-acc r/w-acc x/d-acc
                    wp smep smap ac nxe r-w-x cpl x86-2))))
  :hints (("Goal" :use ((:instance xlate-equiv-memory-and-ia32e-la-to-pa-page-table))))
  :rule-classes :congruence)

(defthm xlate-equiv-memory-and-mv-nth-1-ia32e-la-to-pa-page-table
  (implies (xlate-equiv-memory x86-1 x86-2)
           (equal (mv-nth
                   1
                   (ia32e-la-to-pa-page-table
                    lin-addr base-addr u/s-acc r/w-acc x/d-acc
                    wp smep smap ac nxe r-w-x cpl x86-1))
                  (mv-nth
                   1
                   (ia32e-la-to-pa-page-table
                    lin-addr base-addr u/s-acc r/w-acc x/d-acc
                    wp smep smap ac nxe r-w-x cpl x86-2))))
  :hints (("Goal" :use ((:instance xlate-equiv-memory-and-ia32e-la-to-pa-page-table))))
  :rule-classes :congruence)

(defthm xlate-equiv-structures-and-mv-nth-2-ia32e-la-to-pa-page-table
  (implies
   ;; TODO: Can this hypothesis be removed?
   (x86p x86)
   (xlate-equiv-structures
    (mv-nth 2 (ia32e-la-to-pa-page-table
               lin-addr base-addr u/s-acc r/w-acc x/d-acc
               wp smep smap ac nxe r-w-x cpl x86))
    (double-rewrite x86)))
  :hints (("Goal"
           :cases
           ;; Either (page-table-entry-addr lin-addr base-addr) is in
           ;; (gather-all-paging-structure-qword-addresses x86) or it
           ;; is in the rest of the memory. Lemmas like
           ;; (GATHER-ALL-PAGING-STRUCTURE-QWORD-ADDRESSES-WM-LOW-64-ENTRY-ADDR
           ;; and
           ;; XLATE-EQUIV-ENTRIES-AT-QWORD-ADDRESSES-WITH-WM-LOW-64-ENTRY-ADDR)
           ;; and
           ;; (GATHER-ALL-PAGING-STRUCTURE-QWORD-ADDRESSES-WM-LOW-64-DISJOINT
           ;; and
           ;; XLATE-EQUIV-ENTRIES-AT-QWORD-ADDRESSES-WITH-WM-LOW-64-DISJOINT)
           ;; should be applicable in these situations, respectively.
           ((not (disjoint-p (addr-range 8
                                         (page-table-entry-addr (logext 48 lin-addr)
                                                                (logand 18446744073709547520
                                                                        (loghead 52 base-addr))))
                             (open-qword-paddr-list
                              (gather-all-paging-structure-qword-addresses x86)))))
           :in-theory (e/d* (ia32e-la-to-pa-page-table
                             xlate-equiv-structures)
                            (bitops::logand-with-negated-bitmask
                             accessed-bit
                             dirty-bit
                             not
                             MULTIPLE-OF-8-DISJOINT-WITH-ADDR-RANGE-AND-OPEN-QWORD-PADDR-LIST-TO-MEMBER-P)))
          ("Subgoal 1"
           :in-theory (e/d* (ia32e-la-to-pa-page-table
                             xlate-equiv-structures
                             MULTIPLE-OF-8-DISJOINT-WITH-ADDR-RANGE-AND-OPEN-QWORD-PADDR-LIST-TO-MEMBER-P)
                            (bitops::logand-with-negated-bitmask
                             accessed-bit
                             dirty-bit
                             not)))))

(defthm all-mem-except-paging-structures-equal-and-paging-entry-no-page-fault-p
  (all-mem-except-paging-structures-equal
   (mv-nth
    2
    (paging-entry-no-page-fault-p
     structure-type lin-addr entry
     u/s-acc r/w-acc x/d-acc
     wp smep smap ac nxe r-w-x cpl
     x86 ignored))
   x86)
  :hints (("Goal" :in-theory (e/d* (paging-entry-no-page-fault-p
                                    page-fault-exception)
                                   ()))))

(defthm all-mem-except-paging-structures-equal-with-mv-nth-2-ia32e-la-to-pa-page-table
  (implies
   ;; TODO: Can this hypothesis be removed?
   (and (x86p x86)
        (member-p (page-table-entry-addr (logext 48 lin-addr)
                                         (logand 18446744073709547520 (loghead 52 base-addr)))
                  (gather-all-paging-structure-qword-addresses x86)))
   (all-mem-except-paging-structures-equal
    (mv-nth 2 (ia32e-la-to-pa-page-table
               lin-addr base-addr u/s-acc r/w-acc x/d-acc
               wp smep smap ac nxe r-w-x cpl x86))
    (double-rewrite x86)))
  :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa-page-table)
                                   (bitops::logand-with-negated-bitmask
                                    accessed-bit
                                    dirty-bit
                                    not)))))

(defthm xlate-equiv-memory-with-mv-nth-2-ia32e-la-to-pa-page-table
  (implies
   ;; TODO: Can this hypothesis be removed?
   (and (x86p x86)
        (member-p (page-table-entry-addr (logext 48 lin-addr)
                                         (logand 18446744073709547520 (loghead 52 base-addr)))
                  (gather-all-paging-structure-qword-addresses x86)))
   (xlate-equiv-memory
    (mv-nth 2 (ia32e-la-to-pa-page-table
               lin-addr base-addr u/s-acc r/w-acc x/d-acc
               wp smep smap ac nxe r-w-x cpl x86))
    (double-rewrite x86)))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (e/d* (xlate-equiv-memory)
                            (bitops::logand-with-negated-bitmask
                             accessed-bit
                             dirty-bit
                             not)))))

(defthm two-page-table-walks-ia32e-la-to-pa-page-table
  (implies
   ;; TODO: Can this hypothesis be removed?
   (and (x86p x86)
        (member-p (page-table-entry-addr (logext 48 lin-addr-2)
                                         (logand 18446744073709547520 (loghead 52 base-addr-2)))
                  (gather-all-paging-structure-qword-addresses x86)))

   (and

    (equal
     (mv-nth
      0
      (ia32e-la-to-pa-page-table
       lin-addr-1 base-addr-1 u/s-acc-1 r/w-acc-1 x/d-acc-1
       wp-1 smep-1 smap-1 ac-1 nxe-1 r-w-x-1 cpl-1
       (mv-nth
        2
        (ia32e-la-to-pa-page-table
         lin-addr-2 base-addr-2 u/s-acc-2 r/w-acc-2 x/d-acc-2
         wp-2 smep-2 smap-2 ac-2 nxe-2 r-w-x-2 cpl-2
         x86))))
     (mv-nth
      0
      (ia32e-la-to-pa-page-table
       lin-addr-1 base-addr-1 u/s-acc-1 r/w-acc-1 x/d-acc-1
       wp-1 smep-1 smap-1 ac-1 nxe-1 r-w-x-1 cpl-1 x86)))

    (equal
     (mv-nth
      1
      (ia32e-la-to-pa-page-table
       lin-addr-1 base-addr-1 u/s-acc-1 r/w-acc-1 x/d-acc-1
       wp-1 smep-1 smap-1 ac-1 nxe-1 r-w-x-1 cpl-1
       (mv-nth
        2
        (ia32e-la-to-pa-page-table
         lin-addr-2 base-addr-2 u/s-acc-2 r/w-acc-2 x/d-acc-2
         wp-2 smep-2 smap-2 ac-2 nxe-2 r-w-x-2 cpl-2
         x86))))
     (mv-nth
      1
      (ia32e-la-to-pa-page-table
       lin-addr-1 base-addr-1 u/s-acc-1 r/w-acc-1 x/d-acc-1
       wp-1 smep-1 smap-1 ac-1 nxe-1 r-w-x-1 cpl-1 x86)))))

  :hints (("Goal" :in-theory (e/d* () (ia32e-la-to-pa-page-table)))))

(in-theory (e/d* () (ia32e-la-to-pa-page-table)))

;; ======================================================================

;; The following come in useful when reasoning about higher paging
;; structure traversals...

(defthmd gather-all-paging-structure-qword-addresses-with-xlate-equiv-structures
  (implies (and (equal (programmer-level-mode x86) nil)
                (xlate-equiv-structures (double-rewrite x86) (double-rewrite x86-equiv)))
           (equal (gather-all-paging-structure-qword-addresses x86-equiv)
                  (gather-all-paging-structure-qword-addresses x86)))
  :hints
  (("Goal" :in-theory (e/d* (gather-all-paging-structure-qword-addresses
                             xlate-equiv-structures)
                            ()))))

(defthm gather-all-paging-structure-qword-addresses-mv-nth-2-ia32e-la-to-pa-page-table
  (implies (and (x86p x86)
                (not (programmer-level-mode x86)))
           (equal (gather-all-paging-structure-qword-addresses
                   (mv-nth 2 (ia32e-la-to-pa-page-table
                              lin-addr base-addr u/s-acc r/w-acc x/d-acc
                              wp smep smap ac nxe r-w-x cpl x86)))
                  (gather-all-paging-structure-qword-addresses x86)))
  :hints (("Goal"
           :use ((:instance
                  gather-all-paging-structure-qword-addresses-with-xlate-equiv-structures
                  (x86-equiv (mv-nth 2 (ia32e-la-to-pa-page-table
                                        lin-addr base-addr u/s-acc r/w-acc x/d-acc
                                        wp smep smap ac nxe r-w-x cpl x86))))))))


(defthm xlate-equiv-entries-at-qword-addresses-mv-nth-2-ia32e-la-to-pa-page-table
  (implies (and (equal addrs (gather-all-paging-structure-qword-addresses x86))
                (x86p x86)
                (not (programmer-level-mode x86)))
           (equal (xlate-equiv-entries-at-qword-addresses
                   addrs addrs
                   x86
                   (mv-nth 2 (ia32e-la-to-pa-page-table
                              lin-addr base-addr u/s-acc r/w-acc x/d-acc
                              wp smep smap ac nxe r-w-x cpl x86)))
                  (xlate-equiv-entries-at-qword-addresses addrs addrs x86 x86)))
  :hints (("Goal" :in-theory (e/d* ()
                                   (xlate-equiv-structures-and-xlate-equiv-entries-at-qword-addresses
                                    booleanp-of-xlate-equiv-entries-at-qword-addresses))
           :use ((:instance xlate-equiv-structures-and-xlate-equiv-entries-at-qword-addresses
                            (addrs (gather-all-paging-structure-qword-addresses x86))
                            (x86 x86)
                            (x86-equiv
                             (mv-nth 2 (ia32e-la-to-pa-page-table
                                        lin-addr base-addr u/s-acc r/w-acc x/d-acc
                                        wp smep smap ac nxe r-w-x cpl x86))))
                 (:instance booleanp-of-xlate-equiv-entries-at-qword-addresses
                            (addrs (gather-all-paging-structure-qword-addresses x86))
                            (x x86)
                            (y x86))
                 (:instance booleanp-of-xlate-equiv-entries-at-qword-addresses
                            (addrs (gather-all-paging-structure-qword-addresses x86))
                            (x x86)
                            (y (mv-nth 2 (ia32e-la-to-pa-page-table
                                          lin-addr base-addr u/s-acc r/w-acc x/d-acc
                                          wp smep smap ac nxe r-w-x cpl x86))))))))

;; ======================================================================
