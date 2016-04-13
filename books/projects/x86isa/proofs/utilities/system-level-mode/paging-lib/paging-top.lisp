;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")
(include-book "pml4-table-lemmas" :ttags :all)

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
   ;; TODO: Can this hypothesis be removed?
   (x86p x86)
   (xlate-equiv-structures (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x cpl x86))
                           (double-rewrite x86)))
  :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa) ()))))

(defthm all-mem-except-paging-structures-equal-with-mv-nth-2-ia32e-la-to-pa
  (implies
   ;; TODO: Can this hypothesis be removed?
   (and (x86p x86)
        (member-p (pml4-table-entry-addr (logext 48 lin-addr)
                                         (logand 18446744073709547520
                                                 (loghead 52
                                                          (ash (loghead 40 (logtail 12 (xr :ctr *cr3* x86)))
                                                               12))))
                  (gather-all-paging-structure-qword-addresses x86))

        (member-p
         (page-dir-ptr-table-entry-addr
          (logext 48 lin-addr)
          (ash
           (loghead
            40
            (logtail
             12
             (rm-low-64 (pml4-table-entry-addr
                         (logext 48 lin-addr)
                         (binary-logand 18446744073709547520
                                        (loghead 52 (ash (loghead 40 (logtail 12 (xr :ctr *cr3* x86))) 12))))
                        x86)))
           12))
         (gather-all-paging-structure-qword-addresses x86))

        (if (equal
             (page-size
              (rm-low-64
               (page-dir-ptr-table-entry-addr
                (logext 48 lin-addr)
                (ash
                 (loghead
                  40
                  (logtail
                   12
                   (rm-low-64 (pml4-table-entry-addr
                               (logext 48 lin-addr)
                               (binary-logand 18446744073709547520
                                              (loghead 52 (ash (loghead 40 (logtail 12 (xr :ctr *cr3* x86))) 12))))
                              x86)))
                 12))
               x86))
             0)
            (if
                (member-p
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
                       (ash
                        (loghead
                         40
                         (logtail
                          12
                          (rm-low-64
                           (pml4-table-entry-addr
                            (logext 48 lin-addr)
                            (binary-logand 18446744073709547520
                                           (loghead 52 (ash (loghead 40 (logtail 12 (xr :ctr *cr3* x86))) 12))))
                           x86)))
                        12))
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
                           (rm-low-64
                            (page-dir-ptr-table-entry-addr
                             (logext 48 lin-addr)
                             (ash
                              (loghead
                               40
                               (logtail
                                12
                                (rm-low-64
                                 (pml4-table-entry-addr
                                  (logext 48 lin-addr)
                                  (binary-logand 18446744073709547520
                                                 (loghead 52 (ash (loghead 40 (logtail 12 (xr :ctr *cr3* x86))) 12))))
                                 x86)))
                              12))
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
                                (ash
                                 (loghead
                                  40
                                  (logtail
                                   12
                                   (rm-low-64
                                    (pml4-table-entry-addr
                                     (logext 48 lin-addr)
                                     (binary-logand 18446744073709547520
                                                    (loghead 52 (ash (loghead 40 (logtail 12 (xr :ctr *cr3* x86))) 12))))
                                    x86)))
                                 12))
                               x86)))
                            12))
                          x86)))
                       12))
                     (gather-all-paging-structure-qword-addresses x86))
                  t)
              nil)
          t))
   (all-mem-except-paging-structures-equal
    (mv-nth 2 (ia32e-la-to-pa
               lin-addr
               r-w-x cpl x86))
    (double-rewrite x86)))
  :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa)
                                   (bitops::logand-with-negated-bitmask
                                    accessed-bit
                                    dirty-bit
                                    not)))))

(defthm xlate-equiv-memory-with-mv-nth-2-ia32e-la-to-pa
  (implies
   ;; TODO: Can this hypothesis be removed?
   (and (x86p x86)
        (member-p (pml4-table-entry-addr (logext 48 lin-addr)
                                         (logand 18446744073709547520
                                                 (loghead 52
                                                          (ash (loghead 40 (logtail 12 (xr :ctr *cr3* x86)))
                                                               12))))
                  (gather-all-paging-structure-qword-addresses x86))

        (member-p
         (page-dir-ptr-table-entry-addr
          (logext 48 lin-addr)
          (ash
           (loghead
            40
            (logtail
             12
             (rm-low-64 (pml4-table-entry-addr
                         (logext 48 lin-addr)
                         (binary-logand 18446744073709547520
                                        (loghead 52 (ash (loghead 40 (logtail 12 (xr :ctr *cr3* x86))) 12))))
                        x86)))
           12))
         (gather-all-paging-structure-qword-addresses x86))

        (if (equal
             (page-size
              (rm-low-64
               (page-dir-ptr-table-entry-addr
                (logext 48 lin-addr)
                (ash
                 (loghead
                  40
                  (logtail
                   12
                   (rm-low-64 (pml4-table-entry-addr
                               (logext 48 lin-addr)
                               (binary-logand 18446744073709547520
                                              (loghead 52 (ash (loghead 40 (logtail 12 (xr :ctr *cr3* x86))) 12))))
                              x86)))
                 12))
               x86))
             0)
            (if
                (member-p
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
                       (ash
                        (loghead
                         40
                         (logtail
                          12
                          (rm-low-64
                           (pml4-table-entry-addr
                            (logext 48 lin-addr)
                            (binary-logand 18446744073709547520
                                           (loghead 52 (ash (loghead 40 (logtail 12 (xr :ctr *cr3* x86))) 12))))
                           x86)))
                        12))
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
                           (rm-low-64
                            (page-dir-ptr-table-entry-addr
                             (logext 48 lin-addr)
                             (ash
                              (loghead
                               40
                               (logtail
                                12
                                (rm-low-64
                                 (pml4-table-entry-addr
                                  (logext 48 lin-addr)
                                  (binary-logand 18446744073709547520
                                                 (loghead 52 (ash (loghead 40 (logtail 12 (xr :ctr *cr3* x86))) 12))))
                                 x86)))
                              12))
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
                                (ash
                                 (loghead
                                  40
                                  (logtail
                                   12
                                   (rm-low-64
                                    (pml4-table-entry-addr
                                     (logext 48 lin-addr)
                                     (binary-logand 18446744073709547520
                                                    (loghead 52 (ash (loghead 40 (logtail 12 (xr :ctr *cr3* x86))) 12))))
                                    x86)))
                                 12))
                               x86)))
                            12))
                          x86)))
                       12))
                     (gather-all-paging-structure-qword-addresses x86))
                  t)
              nil)
          t))
   (xlate-equiv-memory
    (mv-nth 2 (ia32e-la-to-pa
               lin-addr
               r-w-x cpl x86))
    (double-rewrite x86)))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (e/d* (xlate-equiv-memory)
                            (bitops::logand-with-negated-bitmask
                             accessed-bit
                             dirty-bit
                             not)))))

(defthm two-page-walks-ia32e-la-to-pa
  (implies
   ;; TODO: Can this hypothesis be removed?
   (and (x86p x86)
        (member-p (pml4-table-entry-addr (logext 48 lin-addr-2)
                                         (logand 18446744073709547520
                                                 (loghead 52
                                                          (ash (loghead 40 (logtail 12 (xr :ctr *cr3* x86)))
                                                               12))))
                  (gather-all-paging-structure-qword-addresses x86))

        (member-p
         (page-dir-ptr-table-entry-addr
          (logext 48 lin-addr-2)
          (ash
           (loghead
            40
            (logtail
             12
             (rm-low-64 (pml4-table-entry-addr
                         (logext 48 lin-addr-2)
                         (binary-logand 18446744073709547520
                                        (loghead 52 (ash (loghead 40 (logtail 12 (xr :ctr *cr3* x86))) 12))))
                        x86)))
           12))
         (gather-all-paging-structure-qword-addresses x86))

        (if (equal
             (page-size
              (rm-low-64
               (page-dir-ptr-table-entry-addr
                (logext 48 lin-addr-2)
                (ash
                 (loghead
                  40
                  (logtail
                   12
                   (rm-low-64 (pml4-table-entry-addr
                               (logext 48 lin-addr-2)
                               (binary-logand 18446744073709547520
                                              (loghead 52 (ash (loghead 40 (logtail 12 (xr :ctr *cr3* x86))) 12))))
                              x86)))
                 12))
               x86))
             0)
            (if
                (member-p
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
                       (ash
                        (loghead
                         40
                         (logtail
                          12
                          (rm-low-64
                           (pml4-table-entry-addr
                            (logext 48 lin-addr-2)
                            (binary-logand 18446744073709547520
                                           (loghead 52 (ash (loghead 40 (logtail 12 (xr :ctr *cr3* x86))) 12))))
                           x86)))
                        12))
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
                           (rm-low-64
                            (page-dir-ptr-table-entry-addr
                             (logext 48 lin-addr-2)
                             (ash
                              (loghead
                               40
                               (logtail
                                12
                                (rm-low-64
                                 (pml4-table-entry-addr
                                  (logext 48 lin-addr-2)
                                  (binary-logand 18446744073709547520
                                                 (loghead 52 (ash (loghead 40 (logtail 12 (xr :ctr *cr3* x86))) 12))))
                                 x86)))
                              12))
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
                                (ash
                                 (loghead
                                  40
                                  (logtail
                                   12
                                   (rm-low-64
                                    (pml4-table-entry-addr
                                     (logext 48 lin-addr-2)
                                     (binary-logand 18446744073709547520
                                                    (loghead 52 (ash (loghead 40 (logtail 12 (xr :ctr *cr3* x86))) 12))))
                                    x86)))
                                 12))
                               x86)))
                            12))
                          x86)))
                       12))
                     (gather-all-paging-structure-qword-addresses x86))
                  t)
              nil)
          t))


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

;; The following come in useful when reasoning about higher paging
;; structure traversals...

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
