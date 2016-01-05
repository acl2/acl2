;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")
(include-book "gather-paging-structures-thms" :ttags :all)

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))

(local (in-theory (e/d (entry-found-p-and-lin-addr
                        entry-found-p-and-good-paging-structures-x86p)
                       (unsigned-byte-p
                        signed-byte-p))))

;; ======================================================================

;; Some lemmas about page-table-entry-no-page-fault-p:

(defthm mv-nth-2-page-table-entry-no-page-fault-p-value-no-error
  (implies (and (not (mv-nth 0
                             (page-table-entry-no-page-fault-p
                              lin-addr entry-1
                              u-s-acc wp smep nxe r-w-x cpl x86)))
                (xlate-equiv-entries (double-rewrite entry-1)
                                     (double-rewrite entry-2))
                (unsigned-byte-p 64 entry-1)
                (unsigned-byte-p 64 entry-2))
           (equal (mv-nth 2
                          (page-table-entry-no-page-fault-p
                           lin-addr entry-2
                           u-s-acc wp smep nxe r-w-x cpl x86))
                  x86))
  :hints (("Goal"
           :use ((:instance xlate-equiv-entries-and-logtail
                            (n 52)
                            (e-1 entry-1)
                            (e-2 entry-2))
                 (:instance xlate-equiv-entries-and-page-execute-disable
                            (e-1 entry-1)
                            (e-2 entry-2)))
           :in-theory (e/d* (page-table-entry-no-page-fault-p
                             page-fault-exception)
                            ()))))

(defthm gather-all-paging-structure-qword-addresses-page-table-entry-no-page-fault-p
  (equal (gather-all-paging-structure-qword-addresses
          (mv-nth 2 (page-table-entry-no-page-fault-p
                     lin-addr entry u-s-acc wp smep nxe r-w-x cpl x86)))
         (gather-all-paging-structure-qword-addresses x86))
  :hints (("Goal" :in-theory (e/d* (page-table-entry-no-page-fault-p
                                    page-fault-exception)
                                   ()))))

(defthm xlate-equiv-entries-at-qword-addresses?-page-table-entry-no-page-fault-p
  (equal
   (xlate-equiv-entries-at-qword-addresses?
    addrs addrs x86
    (mv-nth 2 (page-table-entry-no-page-fault-p
               lin-addr entry u-s-acc wp smep nxe r-w-x cpl x86)))
   (xlate-equiv-entries-at-qword-addresses? addrs addrs x86 x86))
  :hints (("Goal"
           :in-theory (e/d* (xlate-equiv-entries-at-qword-addresses?
                             page-table-entry-no-page-fault-p
                             page-fault-exception)
                            ()))))

(defthm mv-nth-0-page-table-entry-no-page-fault-p-with-xlate-equiv-entries
  (implies (xlate-equiv-entries e-1 e-2)
           (equal (mv-nth
                   0
                   (page-table-entry-no-page-fault-p
                    lin-addr e-1 u-s-acc wp smep nxe r-w-x cpl x86))
                  (mv-nth
                   0
                   (page-table-entry-no-page-fault-p
                    lin-addr e-2 u-s-acc wp smep nxe r-w-x cpl x86))))
  :hints (("Goal"
           :in-theory (e/d* (page-table-entry-no-page-fault-p
                             page-fault-exception)
                            (xlate-equiv-x86s
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
                            (n 52)))))
  :rule-classes :congruence)

(defthm mv-nth-1-page-table-entry-no-page-fault-p-with-xlate-equiv-entries
  (implies (xlate-equiv-entries e-1 e-2)
           (equal (mv-nth
                   1
                   (page-table-entry-no-page-fault-p
                    lin-addr e-1 u-s-acc wp smep nxe r-w-x cpl x86))
                  (mv-nth
                   1
                   (page-table-entry-no-page-fault-p
                    lin-addr e-2 u-s-acc wp smep nxe r-w-x cpl x86))))
  :hints (("Goal"
           :in-theory (e/d* (page-table-entry-no-page-fault-p
                             page-fault-exception)
                            (xlate-equiv-x86s
                             bitops::logand-with-negated-bitmask
                             bitops::logior-equal-0
                             not))))
  :rule-classes :congruence)

(defthm mv-nth-0-page-table-entry-no-page-fault-p-with-xlate-equiv-structures
  (implies (xlate-equiv-structures x86-1 x86-2)
           (equal (mv-nth
                   0
                   (page-table-entry-no-page-fault-p
                    lin-addr entry u-s-acc wp smep nxe r-w-x cpl x86-1))
                  (mv-nth
                   0
                   (page-table-entry-no-page-fault-p
                    lin-addr entry u-s-acc wp smep nxe r-w-x cpl x86-2))))
  :hints (("Goal"
           :in-theory (e/d* (page-table-entry-no-page-fault-p
                             page-fault-exception)
                            (xlate-equiv-x86s
                             bitops::logand-with-negated-bitmask
                             bitops::logior-equal-0
                             not))))
  :rule-classes :congruence)

(defthm mv-nth-1-page-table-entry-no-page-fault-p-with-xlate-equiv-structures
  (implies (xlate-equiv-structures x86-1 x86-2)
           (equal (mv-nth
                   1
                   (page-table-entry-no-page-fault-p
                    lin-addr entry u-s-acc wp smep nxe r-w-x cpl x86-1))
                  (mv-nth
                   1
                   (page-table-entry-no-page-fault-p
                    lin-addr entry u-s-acc wp smep nxe r-w-x cpl x86-2))))
  :hints (("Goal"
           :in-theory (e/d* (page-table-entry-no-page-fault-p
                             page-fault-exception)
                            (xlate-equiv-x86s
                             bitops::logand-with-negated-bitmask
                             bitops::logior-equal-0
                             not))))
  :rule-classes :congruence)

(defthm mv-nth-2-page-table-entry-no-page-fault-p-with-xlate-equiv-x86s
  (implies
   ;; The hyp would need to be changed to

   ;; (equal
   ;;  (mv-nth 0 (page-table-entry-no-page-fault-p lin-addr entry u-s-acc wp smep nxe r-w-x cpl x86))
   ;;  nil)

   ;; if the definition of xlate-equiv-x86s requires the MS and FAULT
   ;; fields to be exactly equal too. If that happens, then the
   ;; theorem xlate-equiv-x86s-with-mv-nth-2-ia32e-la-to-pa-PT would
   ;; also need such a hypothesis.
   (x86p x86)
   (xlate-equiv-x86s
    (mv-nth 2 (page-table-entry-no-page-fault-p lin-addr entry u-s-acc wp smep nxe r-w-x cpl x86))
    (double-rewrite x86)))
  :hints (("Goal" :in-theory (e/d* (page-table-entry-no-page-fault-p
                                    page-fault-exception
                                    xlate-equiv-x86s
                                    xlate-equiv-structures)
                                   ()))))

;; ======================================================================

;; Finally, lemmas about ia32e-la-to-pa-PT:

(defthmd ia32e-la-to-pa-PT-with-xlate-equiv-structures
  (implies (xlate-equiv-structures (double-rewrite x86-1) x86-2)
           (and
            (equal (mv-nth
                    0
                    (ia32e-la-to-pa-PT
                     lin-addr u-s-acc wp smep nxe r-w-x cpl x86-1))
                   (mv-nth
                    0
                    (ia32e-la-to-pa-PT
                     lin-addr u-s-acc wp smep nxe r-w-x cpl x86-2)))
            (equal (mv-nth
                    1
                    (ia32e-la-to-pa-PT
                     lin-addr u-s-acc wp smep nxe r-w-x cpl x86-1))
                   (mv-nth
                    1
                    (ia32e-la-to-pa-PT
                     lin-addr u-s-acc wp smep nxe r-w-x cpl x86-2)))))
  :hints (("Goal"
           :in-theory (e/d* (ia32e-la-to-pa-PT
                             ia32e-la-to-pa-page-table-alt)
                            (xlate-equiv-x86s
                             bitops::logand-with-negated-bitmask
                             bitops::logior-equal-0
                             not))
           :use ((:instance xlate-equiv-entries-and-logtail
                            (e-1 (mv-nth 2 (read-page-table-entry lin-addr x86-1)))
                            (e-2 (mv-nth 2 (read-page-table-entry lin-addr x86-2)))
                            (n 12))))))

(defthm mv-nth-0-ia32e-la-to-pa-PT-with-xlate-equiv-structures
  (implies (xlate-equiv-structures x86-1 x86-2)
           (equal (mv-nth
                   0
                   (ia32e-la-to-pa-PT
                    lin-addr u-s-acc wp smep nxe r-w-x cpl x86-1))
                  (mv-nth
                   0
                   (ia32e-la-to-pa-PT
                    lin-addr u-s-acc wp smep nxe r-w-x cpl x86-2))))
  :hints (("Goal" :use ((:instance ia32e-la-to-pa-pt-with-xlate-equiv-structures))))
  :rule-classes :congruence)

(defthm mv-nth-1-ia32e-la-to-pa-PT-with-xlate-equiv-structures
  (implies (xlate-equiv-structures x86-1 x86-2)
           (equal (mv-nth
                   1
                   (ia32e-la-to-pa-PT
                    lin-addr u-s-acc wp smep nxe r-w-x cpl x86-1))
                  (mv-nth
                   1
                   (ia32e-la-to-pa-PT
                    lin-addr u-s-acc wp smep nxe r-w-x cpl x86-2))))
  :hints (("Goal" :use ((:instance ia32e-la-to-pa-pt-with-xlate-equiv-structures))))
  :rule-classes :congruence)

(defthm xlate-equiv-x86s-with-mv-nth-2-ia32e-la-to-pa-PT
  (xlate-equiv-x86s
   (mv-nth 2 (ia32e-la-to-pa-PT lin-addr u-s-acc wp smep nxe r-w-x cpl x86))
   (double-rewrite x86))
  :hints (("Goal" :do-not '(preprocess)
           :use ((:instance entry-found-p-and-good-paging-structures-x86p))
           :in-theory (e/d* (ia32e-la-to-pa-page-table-alt
                             read-page-table-entry
                             xlate-equiv-x86s)
                            (bitops::logand-with-negated-bitmask
                             accessed-bit
                             dirty-bit
                             not
                             entry-found-p-and-good-paging-structures-x86p
                             no-duplicates-list-p)))))

(defthm two-page-table-walks-ia32e-la-to-pa-PT
  (and

   (equal
    (mv-nth
     0
     (ia32e-la-to-pa-PT
      lin-addr-1 u-s-acc-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
      (mv-nth
       2
       (ia32e-la-to-pa-PT
        lin-addr-2 u-s-acc-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
    (mv-nth
     0
     (ia32e-la-to-pa-PT
      lin-addr-1 u-s-acc-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)))

   (equal
    (mv-nth
     1
     (ia32e-la-to-pa-PT
      lin-addr-1 u-s-acc-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
      (mv-nth
       2
       (ia32e-la-to-pa-PT
        lin-addr-2 u-s-acc-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
    (mv-nth
     1
     (ia32e-la-to-pa-PT
      lin-addr-1 u-s-acc-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86))))

  :hints (("Goal" :in-theory (e/d* () (ia32e-la-to-pa-PT)))))

(in-theory (e/d* () (ia32e-la-to-pa-PT)))

;; ======================================================================

;; The following come in useful when reasoning about higher paging
;; structure traversals...

(defthm gather-all-paging-structure-qword-addresses-mv-nth-2-ia32e-la-to-pa-PT
  (implies (good-paging-structures-x86p (double-rewrite x86))
           (equal (gather-all-paging-structure-qword-addresses
                   (mv-nth 2 (ia32e-la-to-pa-PT lin-addr u-s-acc wp smep nxe r-w-x cpl x86)))
                  (gather-all-paging-structure-qword-addresses x86)))
  :hints (("Goal"
           :in-theory (e/d* () (xlate-equiv-x86s))
           :use ((:instance
                  gather-all-paging-structure-qword-addresses-with-xlate-equiv-structures
                  (x86-equiv (mv-nth 2 (ia32e-la-to-pa-PT lin-addr u-s-acc wp smep nxe r-w-x cpl x86))))))))

(defthm xlate-equiv-entries-at-qword-addresses?-mv-nth-2-ia32e-la-to-pa-PT
  (implies (and (equal addrs (gather-all-paging-structure-qword-addresses x86))
                (good-paging-structures-x86p x86))
           (equal (xlate-equiv-entries-at-qword-addresses?
                   addrs addrs
                   x86
                   (mv-nth 2 (ia32e-la-to-pa-PT lin-addr u-s-acc wp smep nxe r-w-x cpl x86)))
                  (xlate-equiv-entries-at-qword-addresses? addrs addrs x86 x86)))
  :hints (("Goal" :in-theory (e/d* ()
                                   (booleanp-xlate-equiv-entries-at-qword-addresses?
                                    xlate-equiv-structures-and-xlate-equiv-entries-at-qword-addresses?
                                    xlate-equiv-x86s))
           :use ((:instance xlate-equiv-structures-and-xlate-equiv-entries-at-qword-addresses?
                            (addrs (gather-all-paging-structure-qword-addresses x86))
                            (x86 x86)
                            (x86-equiv
                             (mv-nth 2 (ia32e-la-to-pa-PT lin-addr u-s-acc wp smep nxe r-w-x cpl x86))))
                 (:instance booleanp-xlate-equiv-entries-at-qword-addresses?
                            (addrs (gather-all-paging-structure-qword-addresses x86))
                            (x x86)
                            (y x86))
                 (:instance booleanp-xlate-equiv-entries-at-qword-addresses?
                            (addrs (gather-all-paging-structure-qword-addresses x86))
                            (x x86)
                            (y (mv-nth 2 (ia32e-la-to-pa-PT lin-addr u-s-acc wp smep nxe r-w-x cpl x86))))))))

;; ======================================================================
