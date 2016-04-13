;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")
(include-book "page-directory-lemmas" :ttags :all)

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))

(local (in-theory (e/d () (unsigned-byte-p signed-byte-p))))

;; ======================================================================

(defthm xlate-equiv-structures-and-xlate-equiv-entries-rm-low-64-with-page-dir-ptr-table-entry-addr
  (implies (and (xlate-equiv-structures x86-1 x86-2)
                (member-p (page-dir-ptr-table-entry-addr lin-addr base-addr)
                          (gather-all-paging-structure-qword-addresses x86-1)))
           (xlate-equiv-entries (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr) x86-1)
                                (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr) x86-2)))
  :hints (("Goal" :use ((:instance xlate-equiv-structures-and-xlate-equiv-entries
                                   (index (page-dir-ptr-table-entry-addr lin-addr base-addr)))))))

(defthm xlate-equiv-structures-and-logtail-12-rm-low-64-with-page-dir-ptr-table-entry-addr
  (implies (and (xlate-equiv-structures x86-1 x86-2)
                (member-p (page-dir-ptr-table-entry-addr lin-addr base-addr)
                          (gather-all-paging-structure-qword-addresses x86-1)))
           (equal (logtail 12 (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr) x86-1))
                  (logtail 12 (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr) x86-2))))
  :hints (("Goal" :use ((:instance xlate-equiv-entries-and-logtail
                                   (e-1 (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr) x86-1))
                                   (e-2 (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr) x86-2))
                                   (n 12))))))

(defthm xlate-equiv-structures-and-logtail-21-rm-low-64-with-page-dir-ptr-table-entry-addr
  (implies (and (xlate-equiv-structures x86-1 x86-2)
                (member-p (page-dir-ptr-table-entry-addr lin-addr base-addr)
                          (gather-all-paging-structure-qword-addresses x86-1)))
           (equal (logtail 21 (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr) x86-1))
                  (logtail 21 (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr) x86-2))))
  :hints (("Goal" :use ((:instance xlate-equiv-entries-and-logtail
                                   (e-1 (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr) x86-1))
                                   (e-2 (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr) x86-2))
                                   (n 21))))))

(defthm xlate-equiv-structures-and-logtail-30-rm-low-64-with-page-dir-ptr-table-entry-addr
  (implies (and (xlate-equiv-structures x86-1 x86-2)
                (member-p (page-dir-ptr-table-entry-addr lin-addr base-addr)
                          (gather-all-paging-structure-qword-addresses x86-1)))
           (equal (logtail 30 (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr) x86-1))
                  (logtail 30 (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr) x86-2))))
  :hints (("Goal" :use ((:instance xlate-equiv-entries-and-logtail
                                   (e-1 (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr) x86-1))
                                   (e-2 (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr) x86-2))
                                   (n 30))))))

(defthm xlate-equiv-memory-and-xlate-equiv-entries-rm-low-64-with-page-dir-ptr-table-entry-addr
  ;; (page-dir-ptr-table-entry-addr lin-addr base-addr) is either a member of
  ;; gather-all-paging-structure-qword-addresses (because it is a
  ;; quadword-aligned address) or it is a member of the rest of the
  ;; memory (all-mem-except-paging-structures-equal)....
  (implies (xlate-equiv-memory x86-1 x86-2)
           (xlate-equiv-entries (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr) x86-1)
                                (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr) x86-2)))
  :hints (("Goal" :in-theory (e/d* (xlate-equiv-memory) ())
           :cases
           ((not (disjoint-p (addr-range 8 (page-dir-ptr-table-entry-addr lin-addr base-addr))
                             (open-qword-paddr-list
                              (gather-all-paging-structure-qword-addresses x86-1)))))))
  :rule-classes :congruence)

(defthm xlate-equiv-memory-and-logtail-12-rm-low-64-with-page-dir-ptr-table-entry-addr
  (implies (xlate-equiv-memory x86-1 x86-2)
           (equal (logtail 12 (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr) x86-1))
                  (logtail 12 (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr) x86-2))))
  :hints (("Goal"
           :in-theory (e/d* ()
                            (xlate-equiv-memory-and-xlate-equiv-entries-rm-low-64-with-page-dir-ptr-table-entry-addr))
           :use ((:instance xlate-equiv-entries-and-logtail
                            (e-1 (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr) x86-1))
                            (e-2 (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr) x86-2))
                            (n 12))
                 (:instance xlate-equiv-memory-and-xlate-equiv-entries-rm-low-64-with-page-dir-ptr-table-entry-addr))))
  :rule-classes :congruence)

(defthm xlate-equiv-memory-and-logtail-21-rm-low-64-with-page-dir-ptr-table-entry-addr
  (implies (xlate-equiv-memory x86-1 x86-2)
           (equal (logtail 21 (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr) x86-1))
                  (logtail 21 (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr) x86-2))))
  :hints (("Goal"
           :in-theory (e/d* ()
                            (xlate-equiv-memory-and-xlate-equiv-entries-rm-low-64-with-page-dir-ptr-table-entry-addr))
           :use ((:instance xlate-equiv-entries-and-logtail
                            (e-1 (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr) x86-1))
                            (e-2 (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr) x86-2))
                            (n 21))
                 (:instance xlate-equiv-memory-and-xlate-equiv-entries-rm-low-64-with-page-dir-ptr-table-entry-addr))))
  :rule-classes :congruence)

(defthm xlate-equiv-memory-and-logtail-30-rm-low-64-with-page-dir-ptr-table-entry-addr
  (implies (xlate-equiv-memory x86-1 x86-2)
           (equal (logtail 30 (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr) x86-1))
                  (logtail 30 (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr) x86-2))))
  :hints (("Goal"
           :in-theory (e/d* ()
                            (xlate-equiv-memory-and-xlate-equiv-entries-rm-low-64-with-page-dir-ptr-table-entry-addr))
           :use ((:instance xlate-equiv-entries-and-logtail
                            (e-1 (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr) x86-1))
                            (e-2 (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr) x86-2))
                            (n 30))
                 (:instance xlate-equiv-memory-and-xlate-equiv-entries-rm-low-64-with-page-dir-ptr-table-entry-addr))))
  :rule-classes :congruence)

;; ======================================================================

;; Finally, lemmas about ia32e-la-to-pa-page-dir-ptr-table:

(defthmd xlate-equiv-memory-and-ia32e-la-to-pa-page-dir-ptr-table
  (implies (xlate-equiv-memory (double-rewrite x86-1) x86-2)
           (and
            (equal (mv-nth
                    0
                    (ia32e-la-to-pa-page-dir-ptr-table
                     lin-addr base-addr u/s-acc r/w-acc x/d-acc
                     wp smep smap ac nxe r-w-x cpl x86-1))
                   (mv-nth
                    0
                    (ia32e-la-to-pa-page-dir-ptr-table
                     lin-addr base-addr u/s-acc r/w-acc x/d-acc
                     wp smep smap ac nxe r-w-x cpl x86-2)))
            (equal (mv-nth
                    1
                    (ia32e-la-to-pa-page-dir-ptr-table
                     lin-addr base-addr u/s-acc r/w-acc x/d-acc
                     wp smep smap ac nxe r-w-x cpl x86-1))
                   (mv-nth
                    1
                    (ia32e-la-to-pa-page-dir-ptr-table
                     lin-addr base-addr u/s-acc r/w-acc x/d-acc
                     wp smep smap ac nxe r-w-x cpl x86-2)))))
  :hints (("Goal"
           :use ((:instance xlate-equiv-entries-and-page-execute-disable
                            (e-1 (rm-low-64 (page-dir-ptr-table-entry-addr (logext 48 lin-addr)
                                                                           (logand 18446744073709547520
                                                                                   (loghead 52 base-addr)))
                                            x86-1))
                            (e-2 (rm-low-64 (page-dir-ptr-table-entry-addr (logext 48 lin-addr)
                                                                           (logand 18446744073709547520
                                                                                   (loghead 52 base-addr)))
                                            x86-2)))
                 (:instance xlate-equiv-entries-and-page-size
                            (e-1 (rm-low-64 (page-dir-ptr-table-entry-addr (logext 48 lin-addr)
                                                                           (logand 18446744073709547520
                                                                                   (loghead 52 base-addr)))
                                            x86-1))
                            (e-2 (rm-low-64 (page-dir-ptr-table-entry-addr (logext 48 lin-addr)
                                                                           (logand 18446744073709547520
                                                                                   (loghead 52 base-addr)))
                                            x86-2))))
           :in-theory (e/d* (ia32e-la-to-pa-page-dir-ptr-table)
                            (bitops::logand-with-negated-bitmask
                             bitops::logior-equal-0
                             not)))))

(defthm xlate-equiv-memory-and-mv-nth-0-ia32e-la-to-pa-page-dir-ptr-table
  (implies (xlate-equiv-memory x86-1 x86-2)
           (equal (mv-nth
                   0
                   (ia32e-la-to-pa-page-dir-ptr-table
                    lin-addr base-addr u/s-acc r/w-acc x/d-acc
                    wp smep smap ac nxe r-w-x cpl x86-1))
                  (mv-nth
                   0
                   (ia32e-la-to-pa-page-dir-ptr-table
                    lin-addr base-addr u/s-acc r/w-acc x/d-acc
                    wp smep smap ac nxe r-w-x cpl x86-2))))
  :hints (("Goal" :use ((:instance xlate-equiv-memory-and-ia32e-la-to-pa-page-dir-ptr-table))))
  :rule-classes :congruence)

(defthm xlate-equiv-memory-and-mv-nth-1-ia32e-la-to-pa-page-dir-ptr-table
  (implies (xlate-equiv-memory x86-1 x86-2)
           (equal (mv-nth
                   1
                   (ia32e-la-to-pa-page-dir-ptr-table
                    lin-addr base-addr u/s-acc r/w-acc x/d-acc
                    wp smep smap ac nxe r-w-x cpl x86-1))
                  (mv-nth
                   1
                   (ia32e-la-to-pa-page-dir-ptr-table
                    lin-addr base-addr u/s-acc r/w-acc x/d-acc
                    wp smep smap ac nxe r-w-x cpl x86-2))))
  :hints (("Goal" :use ((:instance xlate-equiv-memory-and-ia32e-la-to-pa-page-dir-ptr-table))))
  :rule-classes :congruence)

(defthm xlate-equiv-structures-and-mv-nth-2-ia32e-la-to-pa-page-dir-ptr-table
  (implies
   ;; TODO: Can this hypothesis be removed?
   (x86p x86)
   (xlate-equiv-structures
    (mv-nth 2 (ia32e-la-to-pa-page-dir-ptr-table
               lin-addr base-addr u/s-acc r/w-acc x/d-acc
               wp smep smap ac nxe r-w-x cpl x86))
    (double-rewrite x86)))
  :hints (("Goal"
           :cases
           ;; Either (page-dir-ptr-table-entry-addr lin-addr base-addr) is in
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
                                         (page-dir-ptr-table-entry-addr (logext 48 lin-addr)
                                                                        (logand 18446744073709547520
                                                                                (loghead 52 base-addr))))
                             (open-qword-paddr-list
                              (gather-all-paging-structure-qword-addresses x86)))))
           :in-theory (e/d* (ia32e-la-to-pa-page-dir-ptr-table
                             xlate-equiv-structures)
                            (bitops::logand-with-negated-bitmask
                             accessed-bit
                             dirty-bit
                             not
                             MULTIPLE-OF-8-DISJOINT-WITH-ADDR-RANGE-AND-OPEN-QWORD-PADDR-LIST-TO-MEMBER-P)))
          ("Subgoal 1"
           :in-theory (e/d* (ia32e-la-to-pa-page-dir-ptr-table
                             xlate-equiv-structures
                             MULTIPLE-OF-8-DISJOINT-WITH-ADDR-RANGE-AND-OPEN-QWORD-PADDR-LIST-TO-MEMBER-P)
                            (bitops::logand-with-negated-bitmask
                             accessed-bit
                             dirty-bit
                             not)))))

(defthm all-mem-except-paging-structures-equal-with-mv-nth-2-ia32e-la-to-pa-page-dir-ptr-table
  (implies
   ;; TODO: Can this hypothesis be removed?
   (and (x86p x86)
        (member-p (page-dir-ptr-table-entry-addr (logext 48 lin-addr)
                                                 (logand 18446744073709547520 (loghead 52 base-addr)))
                  (gather-all-paging-structure-qword-addresses x86))
        (if (equal (page-size (rm-low-64 (page-dir-ptr-table-entry-addr
                                          (logext 48 lin-addr)
                                          (logand 18446744073709547520 (loghead 52 base-addr)))
                                         x86))
                   0)
            (and
             (member-p
              (page-directory-entry-addr
               (logext 48 lin-addr)
               (ash
                (loghead
                 40
                 (logtail
                  12
                  (rm-low-64 (page-dir-ptr-table-entry-addr
                              (logext 48 lin-addr)
                              (logand 18446744073709547520
                                      (loghead 52 base-addr)))
                             x86)))
                12))
              (gather-all-paging-structure-qword-addresses x86))
             (if
                 (equal
                  (page-size
                   (rm-low-64
                    (page-directory-entry-addr
                     (logext 48 lin-addr)
                     (ash
                      (loghead
                       40
                       (logtail
                        12
                        (rm-low-64 (page-dir-ptr-table-entry-addr
                                    (logext 48 lin-addr)
                                    (logand 18446744073709547520
                                            (loghead 52 base-addr)))
                                   x86)))
                      12))
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
                      (rm-low-64
                       (page-directory-entry-addr
                        (logext 48 lin-addr)
                        (ash
                         (loghead
                          40
                          (logtail
                           12
                           (rm-low-64
                            (page-dir-ptr-table-entry-addr
                             (logext 48 lin-addr)
                             (logand 18446744073709547520
                                     (loghead 52 base-addr)))
                            x86)))
                         12))
                       x86)))
                    12))
                  (gather-all-paging-structure-qword-addresses x86))
               t))
          t))
   (all-mem-except-paging-structures-equal
    (mv-nth 2 (ia32e-la-to-pa-page-dir-ptr-table
               lin-addr base-addr u/s-acc r/w-acc x/d-acc
               wp smep smap ac nxe r-w-x cpl x86))
    (double-rewrite x86)))
  :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa-page-dir-ptr-table)
                                   (bitops::logand-with-negated-bitmask
                                    accessed-bit
                                    dirty-bit
                                    not)))))

(defthm xlate-equiv-memory-with-mv-nth-2-ia32e-la-to-pa-page-dir-ptr-table
  (implies
   ;; TODO: Can this hypothesis be removed?
   (and (x86p x86)
        (member-p (page-dir-ptr-table-entry-addr (logext 48 lin-addr)
                                                 (logand 18446744073709547520 (loghead 52 base-addr)))
                  (gather-all-paging-structure-qword-addresses x86))
        (if (equal (page-size (rm-low-64 (page-dir-ptr-table-entry-addr
                                          (logext 48 lin-addr)
                                          (logand 18446744073709547520 (loghead 52 base-addr)))
                                         x86))
                   0)
            (and
             (member-p
              (page-directory-entry-addr
               (logext 48 lin-addr)
               (ash
                (loghead
                 40
                 (logtail
                  12
                  (rm-low-64 (page-dir-ptr-table-entry-addr
                              (logext 48 lin-addr)
                              (logand 18446744073709547520
                                      (loghead 52 base-addr)))
                             x86)))
                12))
              (gather-all-paging-structure-qword-addresses x86))
             (if
                 (equal
                  (page-size
                   (rm-low-64
                    (page-directory-entry-addr
                     (logext 48 lin-addr)
                     (ash
                      (loghead
                       40
                       (logtail
                        12
                        (rm-low-64 (page-dir-ptr-table-entry-addr
                                    (logext 48 lin-addr)
                                    (logand 18446744073709547520
                                            (loghead 52 base-addr)))
                                   x86)))
                      12))
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
                      (rm-low-64
                       (page-directory-entry-addr
                        (logext 48 lin-addr)
                        (ash
                         (loghead
                          40
                          (logtail
                           12
                           (rm-low-64
                            (page-dir-ptr-table-entry-addr
                             (logext 48 lin-addr)
                             (logand 18446744073709547520
                                     (loghead 52 base-addr)))
                            x86)))
                         12))
                       x86)))
                    12))
                  (gather-all-paging-structure-qword-addresses x86))
               t))
          t))
   (xlate-equiv-memory
    (mv-nth 2 (ia32e-la-to-pa-page-dir-ptr-table
               lin-addr base-addr u/s-acc r/w-acc x/d-acc
               wp smep smap ac nxe r-w-x cpl x86))
    (double-rewrite x86)))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (e/d* (xlate-equiv-memory)
                            (bitops::logand-with-negated-bitmask
                             accessed-bit
                             dirty-bit
                             not)))))

(defthm two-page-dir-ptr-table-walks-ia32e-la-to-pa-page-dir-ptr-table
  (implies
   ;; TODO: Can this hypothesis be removed?
   (and (x86p x86)
        (member-p (page-dir-ptr-table-entry-addr (logext 48 lin-addr-2)
                                                 (logand 18446744073709547520 (loghead 52 base-addr-2)))
                  (gather-all-paging-structure-qword-addresses x86))
        (if (equal (page-size (rm-low-64 (page-dir-ptr-table-entry-addr
                                          (logext 48 lin-addr-2)
                                          (logand 18446744073709547520 (loghead 52 base-addr-2)))
                                         x86))
                   0)
            (and
             (member-p
              (page-directory-entry-addr
               (logext 48 lin-addr-2)
               (ash
                (loghead
                 40
                 (logtail
                  12
                  (rm-low-64 (page-dir-ptr-table-entry-addr
                              (logext 48 lin-addr-2)
                              (logand 18446744073709547520
                                      (loghead 52 base-addr-2)))
                             x86)))
                12))
              (gather-all-paging-structure-qword-addresses x86))
             (if
                 (equal
                  (page-size
                   (rm-low-64
                    (page-directory-entry-addr
                     (logext 48 lin-addr-2)
                     (ash
                      (loghead
                       40
                       (logtail
                        12
                        (rm-low-64 (page-dir-ptr-table-entry-addr
                                    (logext 48 lin-addr-2)
                                    (logand 18446744073709547520
                                            (loghead 52 base-addr-2)))
                                   x86)))
                      12))
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
                      (rm-low-64
                       (page-directory-entry-addr
                        (logext 48 lin-addr-2)
                        (ash
                         (loghead
                          40
                          (logtail
                           12
                           (rm-low-64
                            (page-dir-ptr-table-entry-addr
                             (logext 48 lin-addr-2)
                             (logand 18446744073709547520
                                     (loghead 52 base-addr-2)))
                            x86)))
                         12))
                       x86)))
                    12))
                  (gather-all-paging-structure-qword-addresses x86))
               t))
          t))

   (and

    (equal
     (mv-nth
      0
      (ia32e-la-to-pa-page-dir-ptr-table
       lin-addr-1 base-addr-1 u/s-acc-1 r/w-acc-1 x/d-acc-1
       wp-1 smep-1 smap-1 ac-1 nxe-1 r-w-x-1 cpl-1
       (mv-nth
        2
        (ia32e-la-to-pa-page-dir-ptr-table
         lin-addr-2 base-addr-2 u/s-acc-2 r/w-acc-2 x/d-acc-2
         wp-2 smep-2 smap-2 ac-2 nxe-2 r-w-x-2 cpl-2
         x86))))
     (mv-nth
      0
      (ia32e-la-to-pa-page-dir-ptr-table
       lin-addr-1 base-addr-1 u/s-acc-1 r/w-acc-1 x/d-acc-1
       wp-1 smep-1 smap-1 ac-1 nxe-1 r-w-x-1 cpl-1 x86)))

    (equal
     (mv-nth
      1
      (ia32e-la-to-pa-page-dir-ptr-table
       lin-addr-1 base-addr-1 u/s-acc-1 r/w-acc-1 x/d-acc-1
       wp-1 smep-1 smap-1 ac-1 nxe-1 r-w-x-1 cpl-1
       (mv-nth
        2
        (ia32e-la-to-pa-page-dir-ptr-table
         lin-addr-2 base-addr-2 u/s-acc-2 r/w-acc-2 x/d-acc-2
         wp-2 smep-2 smap-2 ac-2 nxe-2 r-w-x-2 cpl-2
         x86))))
     (mv-nth
      1
      (ia32e-la-to-pa-page-dir-ptr-table
       lin-addr-1 base-addr-1 u/s-acc-1 r/w-acc-1 x/d-acc-1
       wp-1 smep-1 smap-1 ac-1 nxe-1 r-w-x-1 cpl-1 x86)))))

  :hints (("Goal" :in-theory (e/d* () (ia32e-la-to-pa-page-dir-ptr-table)))))

(in-theory (e/d* () (ia32e-la-to-pa-page-dir-ptr-table)))

;; ======================================================================

;; The following come in useful when reasoning about higher paging
;; structure traversals...

(defthm gather-all-paging-structure-qword-addresses-mv-nth-2-ia32e-la-to-pa-page-dir-ptr-table
  (implies (and (x86p x86)
                (not (programmer-level-mode x86)))
           (equal (gather-all-paging-structure-qword-addresses
                   (mv-nth 2 (ia32e-la-to-pa-page-dir-ptr-table
                              lin-addr base-addr u/s-acc r/w-acc x/d-acc
                              wp smep smap ac nxe r-w-x cpl x86)))
                  (gather-all-paging-structure-qword-addresses x86)))
  :hints (("Goal"
           :use ((:instance
                  gather-all-paging-structure-qword-addresses-with-xlate-equiv-structures
                  (x86-equiv (mv-nth 2 (ia32e-la-to-pa-page-dir-ptr-table
                                        lin-addr base-addr u/s-acc r/w-acc x/d-acc
                                        wp smep smap ac nxe r-w-x cpl x86))))))))


(defthm xlate-equiv-entries-at-qword-addresses-mv-nth-2-ia32e-la-to-pa-page-dir-ptr-table
  (implies (and (equal addrs (gather-all-paging-structure-qword-addresses x86))
                (x86p x86)
                (not (programmer-level-mode x86)))
           (equal (xlate-equiv-entries-at-qword-addresses
                   addrs addrs
                   x86
                   (mv-nth 2 (ia32e-la-to-pa-page-dir-ptr-table
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
                             (mv-nth 2 (ia32e-la-to-pa-page-dir-ptr-table
                                        lin-addr base-addr u/s-acc r/w-acc x/d-acc
                                        wp smep smap ac nxe r-w-x cpl x86))))
                 (:instance booleanp-of-xlate-equiv-entries-at-qword-addresses
                            (addrs (gather-all-paging-structure-qword-addresses x86))
                            (x x86)
                            (y x86))
                 (:instance booleanp-of-xlate-equiv-entries-at-qword-addresses
                            (addrs (gather-all-paging-structure-qword-addresses x86))
                            (x x86)
                            (y (mv-nth 2 (ia32e-la-to-pa-page-dir-ptr-table
                                          lin-addr base-addr u/s-acc r/w-acc x/d-acc
                                          wp smep smap ac nxe r-w-x cpl x86))))))))

;; ======================================================================
