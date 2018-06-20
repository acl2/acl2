;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")
(include-book "page-table-lemmas" :ttags :all)

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))

(local (in-theory (e/d (multiple-of-8-disjoint-with-addr-range-and-open-qword-paddr-list-to-member-p)
                       (unsigned-byte-p signed-byte-p))))

;; ======================================================================

(defthm xlate-equiv-structures-and-xlate-equiv-entries-rm-low-64-with-page-directory-entry-addr
  (implies (and (bind-free
                 (find-an-xlate-equiv-x86
                  'xlate-equiv-structures-and-xlate-equiv-entries-rm-low-64-with-page-directory-entry-addr
                  x86-1 'x86-2
                  mfc state)
                 (x86-2))
                (syntaxp (and (not (eq x86-1 x86-2))
                              ;; x86-1 must be smaller than x86-2.
                              ;; (term-order x86-1 x86-2)
                              ))
                (xlate-equiv-structures (double-rewrite x86-1) x86-2)
                (member-p (page-directory-entry-addr lin-addr base-addr)
                          (gather-all-paging-structure-qword-addresses x86-1)))
           (xlate-equiv-entries (rm-low-64 (page-directory-entry-addr lin-addr base-addr) x86-1)
                                (rm-low-64 (page-directory-entry-addr lin-addr base-addr) x86-2)))
  :hints (("Goal" :use ((:instance xlate-equiv-structures-and-xlate-equiv-entries
                                   (index (page-directory-entry-addr lin-addr base-addr)))))))

(defthm xlate-equiv-structures-and-logtail-12-rm-low-64-with-page-directory-entry-addr
  (implies (and (xlate-equiv-structures (double-rewrite x86-1) x86-2)
                (member-p (page-directory-entry-addr lin-addr base-addr)
                          (gather-all-paging-structure-qword-addresses x86-1)))
           (equal (logtail 12 (rm-low-64 (page-directory-entry-addr lin-addr base-addr) x86-1))
                  (logtail 12 (rm-low-64 (page-directory-entry-addr lin-addr base-addr) x86-2))))
  :hints (("Goal" :use ((:instance xlate-equiv-entries-and-logtail
                                   (e-1 (rm-low-64 (page-directory-entry-addr lin-addr base-addr) x86-1))
                                   (e-2 (rm-low-64 (page-directory-entry-addr lin-addr base-addr) x86-2))
                                   (n 12))))))

(defthm xlate-equiv-structures-and-logtail-21-rm-low-64-with-page-directory-entry-addr
  (implies (and (xlate-equiv-structures (double-rewrite x86-1) x86-2)
                (member-p (page-directory-entry-addr lin-addr base-addr)
                          (gather-all-paging-structure-qword-addresses x86-1)))
           (equal (logtail 21 (rm-low-64 (page-directory-entry-addr lin-addr base-addr) x86-1))
                  (logtail 21 (rm-low-64 (page-directory-entry-addr lin-addr base-addr) x86-2))))
  :hints (("Goal" :use ((:instance xlate-equiv-entries-and-logtail
                                   (e-1 (rm-low-64 (page-directory-entry-addr lin-addr base-addr) x86-1))
                                   (e-2 (rm-low-64 (page-directory-entry-addr lin-addr base-addr) x86-2))
                                   (n 21))))))

(defthm xlate-equiv-memory-and-xlate-equiv-entries-rm-low-64-with-page-directory-entry-addr-cong
  ;; (page-directory-entry-addr lin-addr base-addr) is either a member of
  ;; gather-all-paging-structure-qword-addresses (because it is a
  ;; quadword-aligned address) or it is a member of the rest of the
  ;; memory (all-mem-except-paging-structures-equal)....
  (implies (xlate-equiv-memory x86-1 x86-2)
           (xlate-equiv-entries (rm-low-64 (page-directory-entry-addr lin-addr base-addr) x86-1)
                                (rm-low-64 (page-directory-entry-addr lin-addr base-addr) x86-2)))
  :hints (("Goal" :in-theory (e/d* (xlate-equiv-memory) ())
           :cases
           ((not (disjoint-p (addr-range 8 (page-directory-entry-addr lin-addr base-addr))
                             (open-qword-paddr-list
                              (gather-all-paging-structure-qword-addresses x86-1)))))))
  :rule-classes :congruence)

(defthm xlate-equiv-memory-and-logtail-12-rm-low-64-with-page-directory-entry-addr-cong
  (implies (xlate-equiv-memory x86-1 x86-2)
           (equal (logtail 12 (rm-low-64 (page-directory-entry-addr lin-addr base-addr) x86-1))
                  (logtail 12 (rm-low-64 (page-directory-entry-addr lin-addr base-addr) x86-2))))
  :hints (("Goal"
           :in-theory (e/d* ()
                            (xlate-equiv-memory-and-xlate-equiv-entries-rm-low-64-with-page-directory-entry-addr-cong))
           :use ((:instance xlate-equiv-entries-and-logtail
                            (e-1 (rm-low-64 (page-directory-entry-addr lin-addr base-addr) x86-1))
                            (e-2 (rm-low-64 (page-directory-entry-addr lin-addr base-addr) x86-2))
                            (n 12))
                 (:instance xlate-equiv-memory-and-xlate-equiv-entries-rm-low-64-with-page-directory-entry-addr-cong))))
  :rule-classes :congruence)

(defthm xlate-equiv-memory-and-logtail-21-rm-low-64-with-page-directory-entry-addr-cong
  (implies (xlate-equiv-memory x86-1 x86-2)
           (equal (logtail 21 (rm-low-64 (page-directory-entry-addr lin-addr base-addr) x86-1))
                  (logtail 21 (rm-low-64 (page-directory-entry-addr lin-addr base-addr) x86-2))))
  :hints (("Goal"
           :in-theory (e/d* ()
                            (xlate-equiv-memory-and-xlate-equiv-entries-rm-low-64-with-page-directory-entry-addr-cong))
           :use ((:instance xlate-equiv-entries-and-logtail
                            (e-1 (rm-low-64 (page-directory-entry-addr lin-addr base-addr) x86-1))
                            (e-2 (rm-low-64 (page-directory-entry-addr lin-addr base-addr) x86-2))
                            (n 21))
                 (:instance xlate-equiv-memory-and-xlate-equiv-entries-rm-low-64-with-page-directory-entry-addr-cong))))
  :rule-classes :congruence)

;; ======================================================================

;; Finally, lemmas about ia32e-la-to-pa-page-directory:

(defthm ia32e-la-to-pa-page-directory-in-app-view
  (implies (app-view x86)
           (equal (ia32e-la-to-pa-page-directory
                   lin-addr base-addr u/s-acc r/w-acc x/d-acc wp smep smap ac nxe r-w-x cpl x86)
                  (mv t 0 x86)))
  :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa-page-directory) ()))))

(defthmd xlate-equiv-memory-and-ia32e-la-to-pa-page-directory-2M-pages
  (implies (and (xlate-equiv-memory (double-rewrite x86-1) x86-2)
                (equal
                 (page-size
                  (rm-low-64 (page-directory-entry-addr
                              (logext 48 lin-addr)
                              (logand 18446744073709547520 (loghead 52 base-addr)))
                             x86-2))
                 1))
           (and
            (equal (mv-nth
                    0
                    (ia32e-la-to-pa-page-directory
                     lin-addr base-addr u/s-acc r/w-acc x/d-acc
                     wp smep smap ac nxe r-w-x cpl x86-1))
                   (mv-nth
                    0
                    (ia32e-la-to-pa-page-directory
                     lin-addr base-addr u/s-acc r/w-acc x/d-acc
                     wp smep smap ac nxe r-w-x cpl x86-2)))
            (equal (mv-nth
                    1
                    (ia32e-la-to-pa-page-directory
                     lin-addr base-addr u/s-acc r/w-acc x/d-acc
                     wp smep smap ac nxe r-w-x cpl x86-1))
                   (mv-nth
                    1
                    (ia32e-la-to-pa-page-directory
                     lin-addr base-addr u/s-acc r/w-acc x/d-acc
                     wp smep smap ac nxe r-w-x cpl x86-2)))))
  :hints (("Goal"
           :use ((:instance xlate-equiv-entries-and-page-execute-disable
                            (e-1 (rm-low-64 (page-directory-entry-addr (logext 48 lin-addr)
                                                                       (logand 18446744073709547520
                                                                               (loghead 52 base-addr)))
                                            x86-1))
                            (e-2 (rm-low-64 (page-directory-entry-addr (logext 48 lin-addr)
                                                                       (logand 18446744073709547520
                                                                               (loghead 52 base-addr)))
                                            x86-2)))
                 (:instance xlate-equiv-entries-and-page-size
                            (e-1 (rm-low-64 (page-directory-entry-addr (logext 48 lin-addr)
                                                                       (logand 18446744073709547520
                                                                               (loghead 52 base-addr)))
                                            x86-1))
                            (e-2 (rm-low-64 (page-directory-entry-addr (logext 48 lin-addr)
                                                                       (logand 18446744073709547520
                                                                               (loghead 52 base-addr)))
                                            x86-2))))
           :in-theory (e/d* (ia32e-la-to-pa-page-directory)
                            (bitops::logand-with-negated-bitmask
                             bitops::logior-equal-0
                             not)))))

(defthmd xlate-equiv-memory-and-ia32e-la-to-pa-page-directory-4K-pages
  (implies (and (xlate-equiv-memory (double-rewrite x86-1) x86-2)
                (equal
                 (page-size
                  (rm-low-64 (page-directory-entry-addr
                              (logext 48 lin-addr)
                              (logand 18446744073709547520 (loghead 52 base-addr)))
                             x86-2))
                 0))
           (and
            (equal (mv-nth
                    0
                    (ia32e-la-to-pa-page-directory
                     lin-addr base-addr u/s-acc r/w-acc x/d-acc
                     wp smep smap ac nxe r-w-x cpl x86-1))
                   (mv-nth
                    0
                    (ia32e-la-to-pa-page-directory
                     lin-addr base-addr u/s-acc r/w-acc x/d-acc
                     wp smep smap ac nxe r-w-x cpl x86-2)))
            (equal (mv-nth
                    1
                    (ia32e-la-to-pa-page-directory
                     lin-addr base-addr u/s-acc r/w-acc x/d-acc
                     wp smep smap ac nxe r-w-x cpl x86-1))
                   (mv-nth
                    1
                    (ia32e-la-to-pa-page-directory
                     lin-addr base-addr u/s-acc r/w-acc x/d-acc
                     wp smep smap ac nxe r-w-x cpl x86-2)))))
  :hints (("Goal"
           :use ((:instance xlate-equiv-entries-and-page-execute-disable
                            (e-1 (rm-low-64 (page-directory-entry-addr (logext 48 lin-addr)
                                                                       (logand 18446744073709547520
                                                                               (loghead 52 base-addr)))
                                            x86-1))
                            (e-2 (rm-low-64 (page-directory-entry-addr (logext 48 lin-addr)
                                                                       (logand 18446744073709547520
                                                                               (loghead 52 base-addr)))
                                            x86-2)))
                 (:instance xlate-equiv-entries-and-page-size
                            (e-1 (rm-low-64 (page-directory-entry-addr (logext 48 lin-addr)
                                                                       (logand 18446744073709547520
                                                                               (loghead 52 base-addr)))
                                            x86-1))
                            (e-2 (rm-low-64 (page-directory-entry-addr (logext 48 lin-addr)
                                                                       (logand 18446744073709547520
                                                                               (loghead 52 base-addr)))
                                            x86-2))))
           :in-theory (e/d* (ia32e-la-to-pa-page-directory)
                            (bitops::logand-with-negated-bitmask
                             bitops::logior-equal-0
                             not)))))

(defthmd xlate-equiv-memory-and-ia32e-la-to-pa-page-directory
  (implies (xlate-equiv-memory (double-rewrite x86-1) x86-2)
           (and
            (equal (mv-nth
                    0
                    (ia32e-la-to-pa-page-directory
                     lin-addr base-addr u/s-acc r/w-acc x/d-acc
                     wp smep smap ac nxe r-w-x cpl x86-1))
                   (mv-nth
                    0
                    (ia32e-la-to-pa-page-directory
                     lin-addr base-addr u/s-acc r/w-acc x/d-acc
                     wp smep smap ac nxe r-w-x cpl x86-2)))
            (equal (mv-nth
                    1
                    (ia32e-la-to-pa-page-directory
                     lin-addr base-addr u/s-acc r/w-acc x/d-acc
                     wp smep smap ac nxe r-w-x cpl x86-1))
                   (mv-nth
                    1
                    (ia32e-la-to-pa-page-directory
                     lin-addr base-addr u/s-acc r/w-acc x/d-acc
                     wp smep smap ac nxe r-w-x cpl x86-2)))))
  :hints (("Goal"
           :use ((:instance xlate-equiv-memory-and-ia32e-la-to-pa-page-directory-4K-pages)
                 (:instance xlate-equiv-memory-and-ia32e-la-to-pa-page-directory-2M-pages))
           :in-theory (e/d* ()
                            (bitops::logand-with-negated-bitmask
                             bitops::logior-equal-0
                             not)))))

(defthm xlate-equiv-memory-and-mv-nth-0-ia32e-la-to-pa-page-directory-cong
  (implies (xlate-equiv-memory x86-1 x86-2)
           (equal (mv-nth
                   0
                   (ia32e-la-to-pa-page-directory
                    lin-addr base-addr u/s-acc r/w-acc x/d-acc
                    wp smep smap ac nxe r-w-x cpl x86-1))
                  (mv-nth
                   0
                   (ia32e-la-to-pa-page-directory
                    lin-addr base-addr u/s-acc r/w-acc x/d-acc
                    wp smep smap ac nxe r-w-x cpl x86-2))))
  :hints (("Goal" :use ((:instance xlate-equiv-memory-and-ia32e-la-to-pa-page-directory))))
  :rule-classes :congruence)

(defthm xlate-equiv-memory-and-mv-nth-1-ia32e-la-to-pa-page-directory-cong
  (implies (xlate-equiv-memory x86-1 x86-2)
           (equal (mv-nth
                   1
                   (ia32e-la-to-pa-page-directory
                    lin-addr base-addr u/s-acc r/w-acc x/d-acc
                    wp smep smap ac nxe r-w-x cpl x86-1))
                  (mv-nth
                   1
                   (ia32e-la-to-pa-page-directory
                    lin-addr base-addr u/s-acc r/w-acc x/d-acc
                    wp smep smap ac nxe r-w-x cpl x86-2))))
  :hints (("Goal" :use ((:instance xlate-equiv-memory-and-ia32e-la-to-pa-page-directory))))
  :rule-classes :congruence)

(defthm xlate-equiv-structures-and-mv-nth-2-ia32e-la-to-pa-page-directory
  (xlate-equiv-structures
   (mv-nth 2 (ia32e-la-to-pa-page-directory
              lin-addr base-addr u/s-acc r/w-acc x/d-acc
              wp smep smap ac nxe r-w-x cpl x86))
   (double-rewrite x86))
  :hints (("Goal"
           :cases
           ;; Either (page-directory-entry-addr lin-addr base-addr) is in
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
                                         (page-directory-entry-addr (logext 48 lin-addr)
                                                                    (logand 18446744073709547520
                                                                            (loghead 52 base-addr))))
                             (open-qword-paddr-list
                              (gather-all-paging-structure-qword-addresses x86)))))
           :in-theory (e/d* (ia32e-la-to-pa-page-directory
                             xlate-equiv-structures
                             multiple-of-8-disjoint-with-addr-range-and-open-qword-paddr-list-to-member-p)
                            (bitops::logand-with-negated-bitmask
                             accessed-bit
                             dirty-bit
                             not)))))

(defthmd xlate-equiv-structures-and-two-mv-nth-2-ia32e-la-to-pa-page-directory-cong
  (implies (xlate-equiv-structures x86-1 x86-2)
           (xlate-equiv-structures
            (mv-nth 2 (ia32e-la-to-pa-page-directory
                       lin-addr base-addr u/s-acc r/w-acc x/d-acc
                       wp smep smap ac nxe r-w-x cpl x86-1))
            (mv-nth 2 (ia32e-la-to-pa-page-directory
                       lin-addr base-addr u/s-acc r/w-acc x/d-acc
                       wp smep smap ac nxe r-w-x cpl x86-2))))
  :rule-classes :congruence)

(defthm all-mem-except-paging-structures-equal-with-mv-nth-2-ia32e-la-to-pa-page-directory
  (implies
   (and (member-p (page-directory-entry-addr (logext 48 lin-addr)
                                             (logand 18446744073709547520 (loghead 52 base-addr)))
                  (gather-all-paging-structure-qword-addresses x86))
        (if (equal (page-size (rm-low-64 (page-directory-entry-addr
                                          (logext 48 lin-addr)
                                          (logand 18446744073709547520 (loghead 52 base-addr)))
                                         x86))
                   0)
            (member-p
             (page-table-entry-addr
              (logext 48 lin-addr)
              (ash
               (loghead
                40
                (logtail
                 12
                 (rm-low-64 (page-directory-entry-addr
                             (logext 48 lin-addr)
                             (logand 18446744073709547520 (loghead 52 base-addr)))
                            x86)))
               12))
             (gather-all-paging-structure-qword-addresses x86))
          t))
   (all-mem-except-paging-structures-equal
    (mv-nth 2 (ia32e-la-to-pa-page-directory
               lin-addr base-addr u/s-acc r/w-acc x/d-acc
               wp smep smap ac nxe r-w-x cpl x86))
    (double-rewrite x86)))
  :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa-page-directory)
                                   (bitops::logand-with-negated-bitmask
                                    accessed-bit
                                    dirty-bit
                                    not)))))

(defthmd all-mem-except-paging-structures-equal-with-two-mv-nth-2-ia32e-la-to-pa-page-directory
  (implies
   (and (all-mem-except-paging-structures-equal x86-1 x86-2)
        (member-p (page-directory-entry-addr (logext 48 lin-addr)
                                             (logand 18446744073709547520 (loghead 52 base-addr)))
                  (gather-all-paging-structure-qword-addresses x86-1))
        (if (equal (page-size (rm-low-64 (page-directory-entry-addr
                                          (logext 48 lin-addr)
                                          (logand 18446744073709547520 (loghead 52 base-addr)))
                                         x86-1))
                   0)
            (member-p
             (page-table-entry-addr
              (logext 48 lin-addr)
              (ash
               (loghead
                40
                (logtail
                 12
                 (rm-low-64 (page-directory-entry-addr
                             (logext 48 lin-addr)
                             (logand 18446744073709547520 (loghead 52 base-addr)))
                            x86-1)))
               12))
             (gather-all-paging-structure-qword-addresses x86-1))
          t)
        (member-p (page-directory-entry-addr (logext 48 lin-addr)
                                             (logand 18446744073709547520 (loghead 52 base-addr)))
                  (gather-all-paging-structure-qword-addresses x86-2))
        (if (equal (page-size (rm-low-64 (page-directory-entry-addr
                                          (logext 48 lin-addr)
                                          (logand 18446744073709547520 (loghead 52 base-addr)))
                                         x86-2))
                   0)
            (member-p
             (page-table-entry-addr
              (logext 48 lin-addr)
              (ash
               (loghead
                40
                (logtail
                 12
                 (rm-low-64 (page-directory-entry-addr
                             (logext 48 lin-addr)
                             (logand 18446744073709547520 (loghead 52 base-addr)))
                            x86-2)))
               12))
             (gather-all-paging-structure-qword-addresses x86-2))
          t))
   (all-mem-except-paging-structures-equal
    (mv-nth 2 (ia32e-la-to-pa-page-directory
               lin-addr base-addr u/s-acc r/w-acc x/d-acc
               wp smep smap ac nxe r-w-x cpl x86-1))
    (mv-nth 2 (ia32e-la-to-pa-page-directory
               lin-addr base-addr u/s-acc r/w-acc x/d-acc
               wp smep smap ac nxe r-w-x cpl x86-2)))))

(defthm xlate-equiv-memory-with-mv-nth-2-ia32e-la-to-pa-page-directory
  (implies
   ;; without the 64-bit mode hyp, this theorem is not true,
   ;; because ia32e-la-to-pa-page-directory may mark bits in the state
   (and (64-bit-modep x86)
        (member-p (page-directory-entry-addr (logext 48 lin-addr)
                                             (logand 18446744073709547520 (loghead 52 base-addr)))
                  (gather-all-paging-structure-qword-addresses x86))
        (if (equal (page-size (rm-low-64 (page-directory-entry-addr
                                          (logext 48 lin-addr)
                                          (logand 18446744073709547520 (loghead 52 base-addr)))
                                         x86))
                   0)
            (member-p
             (page-table-entry-addr
              (logext 48 lin-addr)
              (ash
               (loghead
                40
                (logtail
                 12
                 (rm-low-64 (page-directory-entry-addr
                             (logext 48 lin-addr)
                             (logand 18446744073709547520 (loghead 52 base-addr)))
                            x86)))
               12))
             (gather-all-paging-structure-qword-addresses x86))
          t))
   (xlate-equiv-memory
    (mv-nth 2 (ia32e-la-to-pa-page-directory
               lin-addr base-addr u/s-acc r/w-acc x/d-acc
               wp smep smap ac nxe r-w-x cpl x86))
    (double-rewrite x86)))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (e/d* (xlate-equiv-memory)
                            (bitops::logand-with-negated-bitmask
                             accessed-bit
                             dirty-bit
                             not)))))

(defthmd xlate-equiv-memory-with-two-mv-nth-2-ia32e-la-to-pa-page-directory
  (implies
   (and (xlate-equiv-memory (double-rewrite x86-1) x86-2)
        (member-p (page-directory-entry-addr (logext 48 lin-addr)
                                             (logand 18446744073709547520 (loghead 52 base-addr)))
                  (gather-all-paging-structure-qword-addresses x86-1))
        (if (equal (page-size (rm-low-64 (page-directory-entry-addr
                                          (logext 48 lin-addr)
                                          (logand 18446744073709547520 (loghead 52 base-addr)))
                                         x86-1))
                   0)
            (member-p
             (page-table-entry-addr
              (logext 48 lin-addr)
              (ash
               (loghead
                40
                (logtail
                 12
                 (rm-low-64 (page-directory-entry-addr
                             (logext 48 lin-addr)
                             (logand 18446744073709547520 (loghead 52 base-addr)))
                            x86-1)))
               12))
             (gather-all-paging-structure-qword-addresses x86-1))
          t)
        (member-p (page-directory-entry-addr (logext 48 lin-addr)
                                             (logand 18446744073709547520 (loghead 52 base-addr)))
                  (gather-all-paging-structure-qword-addresses x86-2))
        (if (equal (page-size (rm-low-64 (page-directory-entry-addr
                                          (logext 48 lin-addr)
                                          (logand 18446744073709547520 (loghead 52 base-addr)))
                                         x86-2))
                   0)
            (member-p
             (page-table-entry-addr
              (logext 48 lin-addr)
              (ash
               (loghead
                40
                (logtail
                 12
                 (rm-low-64 (page-directory-entry-addr
                             (logext 48 lin-addr)
                             (logand 18446744073709547520 (loghead 52 base-addr)))
                            x86-2)))
               12))
             (gather-all-paging-structure-qword-addresses x86-2))
          t))
   (xlate-equiv-memory
    (mv-nth 2 (ia32e-la-to-pa-page-directory
               lin-addr base-addr u/s-acc r/w-acc x/d-acc
               wp smep smap ac nxe r-w-x cpl x86-1))
    (mv-nth 2 (ia32e-la-to-pa-page-directory
               lin-addr base-addr u/s-acc r/w-acc x/d-acc
               wp smep smap ac nxe r-w-x cpl x86-2))))
  ;; add the following after adding 64-bit mode hyp to previous theorem:
  :hints (("Goal" :in-theory (enable xlate-equiv-memory))))

(defthm two-page-directory-walks-ia32e-la-to-pa-page-directory
  (implies
   ;; the 64-bit mode hyp makes the proof of this theorem easy
   ;; (via xlate-equiv-memory-with-mv-nth-2-ia32e-la-to-pa-page-directory above),
   ;; but could this hyp be removed from here?
   (and (64-bit-modep x86)
        (member-p (page-directory-entry-addr (logext 48 lin-addr-2)
                                             (logand 18446744073709547520 (loghead 52 base-addr-2)))
                  (gather-all-paging-structure-qword-addresses x86))
        (if (equal (page-size (rm-low-64 (page-directory-entry-addr
                                          (logext 48 lin-addr-2)
                                          (logand 18446744073709547520 (loghead 52 base-addr-2)))
                                         x86))
                   0)
            (member-p
             (page-table-entry-addr
              (logext 48 lin-addr-2)
              (ash
               (loghead
                40
                (logtail
                 12
                 (rm-low-64 (page-directory-entry-addr
                             (logext 48 lin-addr-2)
                             (logand 18446744073709547520 (loghead 52 base-addr-2)))
                            x86)))
               12))
             (gather-all-paging-structure-qword-addresses x86))
          t))

   (and

    (equal
     (mv-nth
      0
      (ia32e-la-to-pa-page-directory
       lin-addr-1 base-addr-1 u/s-acc-1 r/w-acc-1 x/d-acc-1
       wp-1 smep-1 smap-1 ac-1 nxe-1 r-w-x-1 cpl-1
       (mv-nth
        2
        (ia32e-la-to-pa-page-directory
         lin-addr-2 base-addr-2 u/s-acc-2 r/w-acc-2 x/d-acc-2
         wp-2 smep-2 smap-2 ac-2 nxe-2 r-w-x-2 cpl-2
         x86))))
     (mv-nth
      0
      (ia32e-la-to-pa-page-directory
       lin-addr-1 base-addr-1 u/s-acc-1 r/w-acc-1 x/d-acc-1
       wp-1 smep-1 smap-1 ac-1 nxe-1 r-w-x-1 cpl-1 x86)))

    (equal
     (mv-nth
      1
      (ia32e-la-to-pa-page-directory
       lin-addr-1 base-addr-1 u/s-acc-1 r/w-acc-1 x/d-acc-1
       wp-1 smep-1 smap-1 ac-1 nxe-1 r-w-x-1 cpl-1
       (mv-nth
        2
        (ia32e-la-to-pa-page-directory
         lin-addr-2 base-addr-2 u/s-acc-2 r/w-acc-2 x/d-acc-2
         wp-2 smep-2 smap-2 ac-2 nxe-2 r-w-x-2 cpl-2
         x86))))
     (mv-nth
      1
      (ia32e-la-to-pa-page-directory
       lin-addr-1 base-addr-1 u/s-acc-1 r/w-acc-1 x/d-acc-1
       wp-1 smep-1 smap-1 ac-1 nxe-1 r-w-x-1 cpl-1 x86)))))

  :hints (("Goal" :in-theory (e/d* () (ia32e-la-to-pa-page-directory)))))

(in-theory (e/d* () (ia32e-la-to-pa-page-directory)))

;; ======================================================================

;; The following come in useful when reasoning about higher paging
;; structure traversals...

(defthm gather-all-paging-structure-qword-addresses-mv-nth-2-ia32e-la-to-pa-page-directory
  (equal (gather-all-paging-structure-qword-addresses
          (mv-nth 2 (ia32e-la-to-pa-page-directory
                     lin-addr base-addr u/s-acc r/w-acc x/d-acc
                     wp smep smap ac nxe r-w-x cpl x86)))
         (gather-all-paging-structure-qword-addresses x86))
  :hints (("Goal"
           :use ((:instance
                  gather-all-paging-structure-qword-addresses-with-xlate-equiv-structures
                  (x86-equiv (mv-nth 2 (ia32e-la-to-pa-page-directory
                                        lin-addr base-addr u/s-acc r/w-acc x/d-acc
                                        wp smep smap ac nxe r-w-x cpl x86))))))))


(defthm xlate-equiv-entries-at-qword-addresses-mv-nth-2-ia32e-la-to-pa-page-directory
  (implies (equal addrs (gather-all-paging-structure-qword-addresses x86))
           (equal (xlate-equiv-entries-at-qword-addresses
                   addrs addrs
                   x86
                   (mv-nth 2 (ia32e-la-to-pa-page-directory
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
                             (mv-nth 2 (ia32e-la-to-pa-page-directory
                                        lin-addr base-addr u/s-acc r/w-acc x/d-acc
                                        wp smep smap ac nxe r-w-x cpl x86))))
                 (:instance booleanp-of-xlate-equiv-entries-at-qword-addresses
                            (addrs (gather-all-paging-structure-qword-addresses x86))
                            (x x86)
                            (y x86))
                 (:instance booleanp-of-xlate-equiv-entries-at-qword-addresses
                            (addrs (gather-all-paging-structure-qword-addresses x86))
                            (x x86)
                            (y (mv-nth 2 (ia32e-la-to-pa-page-directory
                                          lin-addr base-addr u/s-acc r/w-acc x/d-acc
                                          wp smep smap ac nxe r-w-x cpl x86))))))))

;; ======================================================================
