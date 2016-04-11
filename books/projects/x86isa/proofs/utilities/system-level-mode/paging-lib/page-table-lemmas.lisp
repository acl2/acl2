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

;; Finally, lemmas about ia32e-la-to-pa-page-table:

(i-am-here)

(defthm rm-low-64-in-programmer-level-mode
  (implies (programmer-level-mode x86)
           (equal (rm-low-64 p-addr x86) 0))
  :hints (("Goal" :in-theory (e/d* (rm-low-64) ()))))

(defthm xlate-equiv-structures-and-logtail-12-rm-low-64-with-page-table-entry-addr
  ;; (page-table-entry-addr lin-addr base-addr) is either a member of
  ;; gather-all-paging-structure-qword-addresses (because it is a
  ;; quadword-aligned address) or it is a member of the rest of the
  ;; memory....

  ;; I need to include in xlate-equiv-structures that the rest of the
  ;; memory in two xlate-equiv-structures is exactly equal.
  (implies (xlate-equiv-structures x86-1 x86-2)
           (equal (logtail 12 (rm-low-64 (page-table-entry-addr lin-addr base-addr) x86-1))
                  (logtail 12 (rm-low-64 (page-table-entry-addr lin-addr base-addr) x86-2))))
  :hints (("Goal" :in-theory (e/d* (page-table-entry-addr xlate-equiv-structures)
                                   ())))
  :rule-classes :congruence)

(defthmd ia32e-la-to-pa-page-table-with-xlate-equiv-structures
  (implies (xlate-equiv-structures (double-rewrite x86-1) x86-2)
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
                             not))
           ;; :use ((:instance xlate-equiv-entries-and-logtail
           ;;                  (e-1 (mv-nth 2 (read-page-table-entry lin-addr x86-1)))
           ;;                  (e-2 (mv-nth 2 (read-page-table-entry lin-addr x86-2)))
           ;;                  (n 12)))
           ))
  :otf-flg t)

(defthm mv-nth-0-ia32e-la-to-pa-page-table-with-xlate-equiv-structures
  (implies (xlate-equiv-structures x86-1 x86-2)
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
  :hints (("Goal" :use ((:instance ia32e-la-to-pa-pt-with-xlate-equiv-structures))))
  :rule-classes :congruence)

(defthm mv-nth-1-ia32e-la-to-pa-page-table-with-xlate-equiv-structures
  (implies (xlate-equiv-structures x86-1 x86-2)
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
  :hints (("Goal" :use ((:instance ia32e-la-to-pa-pt-with-xlate-equiv-structures))))
  :rule-classes :congruence)

(defthm xlate-equiv-structures-with-mv-nth-2-ia32e-la-to-pa-page-table
  (xlate-equiv-structures
   (mv-nth 2 (ia32e-la-to-pa-page-table
              lin-addr base-addr u/s-acc r/w-acc x/d-acc
              wp smep smap ac nxe r-w-x cpl x86))
   (double-rewrite x86))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (e/d* (ia32e-la-to-pa-page-table
                             xlate-equiv-structures)
                            (bitops::logand-with-negated-bitmask
                             accessed-bit
                             dirty-bit
                             not))))
  :otf-flg t)

(defthm two-page-table-walks-ia32e-la-to-pa-page-table
  (and

   (equal
    (mv-nth
     0
     (ia32e-la-to-pa-page-table
      lin-addr-1 u-s-acc-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
      (mv-nth
       2
       (ia32e-la-to-pa-page-table
        lin-addr-2 u-s-acc-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
    (mv-nth
     0
     (ia32e-la-to-pa-page-table
      lin-addr-1 u-s-acc-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)))

   (equal
    (mv-nth
     1
     (ia32e-la-to-pa-page-table
      lin-addr-1 u-s-acc-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
      (mv-nth
       2
       (ia32e-la-to-pa-page-table
        lin-addr-2 u-s-acc-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
    (mv-nth
     1
     (ia32e-la-to-pa-page-table
      lin-addr-1 u-s-acc-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86))))

  :hints (("Goal" :in-theory (e/d* () (ia32e-la-to-pa-page-table)))))

(in-theory (e/d* () (ia32e-la-to-pa-page-table)))

;; ======================================================================

;; The following come in useful when reasoning about higher paging
;; structure traversals...

(defthm gather-all-paging-structure-qword-addresses-mv-nth-2-ia32e-la-to-pa-page-table
  (implies (good-paging-structures-x86p (double-rewrite x86))
           (equal (gather-all-paging-structure-qword-addresses
                   (mv-nth 2 (ia32e-la-to-pa-page-table lin-addr u-s-acc wp smep nxe r-w-x cpl x86)))
                  (gather-all-paging-structure-qword-addresses x86)))
  :hints (("Goal"
           :in-theory (e/d* () (xlate-equiv-x86s))
           :use ((:instance
                  gather-all-paging-structure-qword-addresses-with-xlate-equiv-structures
                  (x86-equiv (mv-nth 2 (ia32e-la-to-pa-page-table lin-addr u-s-acc wp smep nxe r-w-x cpl x86))))))))

(defthm xlate-equiv-entries-at-qword-addresses-mv-nth-2-ia32e-la-to-pa-page-table
  (implies (and (equal addrs (gather-all-paging-structure-qword-addresses x86))
                (good-paging-structures-x86p x86))
           (equal (xlate-equiv-entries-at-qword-addresses
                   addrs addrs
                   x86
                   (mv-nth 2 (ia32e-la-to-pa-page-table lin-addr u-s-acc wp smep nxe r-w-x cpl x86)))
                  (xlate-equiv-entries-at-qword-addresses addrs addrs x86 x86)))
  :hints (("Goal" :in-theory (e/d* ()
                                   (booleanp-xlate-equiv-entries-at-qword-addresses
                                    xlate-equiv-structures-and-xlate-equiv-entries-at-qword-addresses
                                    xlate-equiv-x86s))
           :use ((:instance xlate-equiv-structures-and-xlate-equiv-entries-at-qword-addresses
                            (addrs (gather-all-paging-structure-qword-addresses x86))
                            (x86 x86)
                            (x86-equiv
                             (mv-nth 2 (ia32e-la-to-pa-page-table lin-addr u-s-acc wp smep nxe r-w-x cpl x86))))
                 (:instance booleanp-xlate-equiv-entries-at-qword-addresses
                            (addrs (gather-all-paging-structure-qword-addresses x86))
                            (x x86)
                            (y x86))
                 (:instance booleanp-xlate-equiv-entries-at-qword-addresses
                            (addrs (gather-all-paging-structure-qword-addresses x86))
                            (x x86)
                            (y (mv-nth 2 (ia32e-la-to-pa-page-table lin-addr u-s-acc wp smep nxe r-w-x cpl x86))))))))

;; ======================================================================
