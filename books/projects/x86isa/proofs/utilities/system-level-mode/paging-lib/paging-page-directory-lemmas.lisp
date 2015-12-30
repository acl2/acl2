;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")
(include-book "paging-page-table-lemmas" :ttags :all)

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))

(local (in-theory (e/d (entry-found-p-and-lin-addr
                        entry-found-p-and-good-paging-structures-x86p)
                       (unsigned-byte-p
                        signed-byte-p))))

;; ======================================================================

;; Some lemmas about paging-entry-no-page-fault-p-value-no-error:

(defthmd not-good-paging-structures-x86p-and-ia32e-la-to-pa-PD
  (implies (not (good-paging-structures-x86p x86))
           (and (equal (mv-nth
                        0
                        (ia32e-la-to-pa-PD
                         lin-addr wp smep nxe r-w-x cpl x86))
                       t)
                (equal (mv-nth
                        1
                        (ia32e-la-to-pa-PD
                         lin-addr wp smep nxe r-w-x cpl x86))
                       0)
                (equal (mv-nth
                        2
                        (ia32e-la-to-pa-PD
                         lin-addr wp smep nxe r-w-x cpl x86))
                       x86))))

(local (in-theory (e/d (not-good-paging-structures-x86p-and-ia32e-la-to-pa-PD)
                       ())))

(defthm mv-nth-2-paging-entry-no-page-fault-p-value-no-error
  (implies (not (mv-nth 0 (paging-entry-no-page-fault-p
                           lin-addr entry wp smep nxe r-w-x cpl x86)))
           (equal
            (mv-nth 2 (paging-entry-no-page-fault-p
                       lin-addr entry wp smep nxe r-w-x cpl x86))
            x86))
  :hints (("Goal" :in-theory (e/d* (paging-entry-no-page-fault-p) ()))))

(defthm gather-all-paging-structure-qword-addresses-paging-entry-no-page-fault-p
  (equal (gather-all-paging-structure-qword-addresses
          (mv-nth 2 (paging-entry-no-page-fault-p
                     lin-addr entry wp smep nxe r-w-x cpl x86)))
         (gather-all-paging-structure-qword-addresses x86))
  :hints (("Goal" :in-theory (e/d* (paging-entry-no-page-fault-p
                                    page-fault-exception)
                                   ()))))

(defthm xlate-equiv-entries-at-qword-addresses?-paging-entry-no-page-fault-p
  (equal
   (xlate-equiv-entries-at-qword-addresses?
    addrs addrs
    x86
    (mv-nth 2 (paging-entry-no-page-fault-p
               lin-addr entry wp smep nxe r-w-x cpl x86)))
   (xlate-equiv-entries-at-qword-addresses? addrs addrs x86 x86))
  :hints (("Goal"
           :in-theory (e/d* (xlate-equiv-entries-at-qword-addresses?
                             paging-entry-no-page-fault-p
                             page-fault-exception)
                            ()))))

(defthm mv-nth-0-paging-entry-no-page-fault-p-with-xlate-equiv-entries
  (implies (xlate-equiv-entries e-1 e-2)
           (equal (mv-nth
                   0
                   (paging-entry-no-page-fault-p
                    lin-addr e-1 wp smep nxe r-w-x cpl x86))
                  (mv-nth
                   0
                   (paging-entry-no-page-fault-p
                    lin-addr e-2 wp smep nxe r-w-x cpl x86))))
  :hints (("Goal"
           :in-theory (e/d* (paging-entry-no-page-fault-p
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
                            (n 13))
                 (:instance xlate-equiv-entries-and-logtail
                            (e-1 (loghead 64 e-1))
                            (e-2 (loghead 64 e-2))
                            (n 52)))))
  :rule-classes :congruence)

(defthm mv-nth-1-paging-entry-no-page-fault-p-with-xlate-equiv-entries
  (implies (xlate-equiv-entries e-1 e-2)
           (equal (mv-nth
                   1
                   (paging-entry-no-page-fault-p
                    lin-addr e-1 wp smep nxe r-w-x cpl x86))
                  (mv-nth
                   1
                   (paging-entry-no-page-fault-p
                    lin-addr e-2 wp smep nxe r-w-x cpl x86))))
  :hints (("Goal"
           :in-theory (e/d* (paging-entry-no-page-fault-p
                             page-fault-exception)
                            (xlate-equiv-x86s
                             bitops::logand-with-negated-bitmask
                             bitops::logior-equal-0
                             not))))
  :rule-classes :congruence)

(defthm mv-nth-0-paging-entry-no-page-fault-p-with-xlate-equiv-x86s
  (implies (xlate-equiv-x86s x86-1 x86-2)
           (equal (mv-nth
                   0
                   (paging-entry-no-page-fault-p
                    lin-addr entry wp smep nxe r-w-x cpl x86-1))
                  (mv-nth
                   0
                   (paging-entry-no-page-fault-p
                    lin-addr entry wp smep nxe r-w-x cpl x86-2))))
  :hints (("Goal"
           :in-theory (e/d* (paging-entry-no-page-fault-p
                             page-fault-exception)
                            (xlate-equiv-x86s
                             bitops::logand-with-negated-bitmask
                             bitops::logior-equal-0
                             not))))
  :rule-classes :congruence)

(defthm mv-nth-1-paging-entry-no-page-fault-p-with-xlate-equiv-x86s
  (implies (xlate-equiv-x86s x86-1 x86-2)
           (equal (mv-nth
                   1
                   (paging-entry-no-page-fault-p
                    lin-addr entry wp smep nxe r-w-x cpl x86-1))
                  (mv-nth
                   1
                   (paging-entry-no-page-fault-p
                    lin-addr entry wp smep nxe r-w-x cpl x86-2))))
  :hints (("Goal"
           :in-theory (e/d* (paging-entry-no-page-fault-p
                             page-fault-exception)
                            (xlate-equiv-x86s
                             bitops::logand-with-negated-bitmask
                             bitops::logior-equal-0
                             not))))
  :rule-classes :congruence)

(defthm xlate-equiv-x86s-with-mv-nth-2-paging-entry-no-page-fault-p
  (implies (x86p x86)
           (xlate-equiv-x86s
            (mv-nth 2 (paging-entry-no-page-fault-p lin-addr entry wp smep nxe r-w-x cpl x86))
            (double-rewrite x86)))
  :hints (("Goal" :in-theory (e/d* (paging-entry-no-page-fault-p
                                    page-fault-exception
                                    xlate-equiv-x86s)
                                   ()))))

;; ======================================================================

;; Finally, some lemmas about ia32e-la-to-pa-PD:

(local
 (defthmd ia32e-la-to-pa-PD-with-xlate-equiv-x86s-2M-pages
   (implies (and (xlate-equiv-x86s x86-1 x86-2)
                 (equal (page-size
                         (mv-nth 2 (read-page-directory-entry lin-addr x86-1)))
                        1))
            (and
             (equal (mv-nth
                     0
                     (ia32e-la-to-pa-PD
                      lin-addr wp smep nxe r-w-x cpl x86-1))
                    (mv-nth
                     0
                     (ia32e-la-to-pa-PD
                      lin-addr wp smep nxe r-w-x cpl x86-2)))
             (equal (mv-nth
                     1
                     (ia32e-la-to-pa-PD
                      lin-addr wp smep nxe r-w-x cpl x86-1))
                    (mv-nth
                     1
                     (ia32e-la-to-pa-PD
                      lin-addr wp smep nxe r-w-x cpl x86-2)))))
   :hints (("Goal"
            :in-theory (e/d* (ia32e-la-to-pa-page-directory-alt
                              entry-found-p-and-lin-addr)
                             (xlate-equiv-x86s
                              bitops::logand-with-negated-bitmask
                              bitops::logior-equal-0))
            :use ((:instance xlate-equiv-entries-and-logtail
                             (e-1 (mv-nth 2 (read-page-directory-entry lin-addr x86-1)))
                             (e-2 (mv-nth 2 (read-page-directory-entry lin-addr x86-2)))
                             (n 21))
                  (:instance xlate-equiv-entries-and-page-size
                             (e-1 (mv-nth 2 (read-page-directory-entry lin-addr x86-1)))
                             (e-2 (mv-nth 2 (read-page-directory-entry lin-addr x86-2)))))))))

(local
 (defthmd ia32e-la-to-pa-PD-with-xlate-equiv-x86s-4K-pages
   (implies (and (xlate-equiv-x86s x86-1 x86-2)
                 (equal
                  (page-size
                   (mv-nth 2 (read-page-directory-entry lin-addr x86-1)))
                  0))
            (and
             (equal (mv-nth
                     0
                     (ia32e-la-to-pa-PD
                      lin-addr wp smep nxe r-w-x cpl x86-1))
                    (mv-nth
                     0
                     (ia32e-la-to-pa-PD
                      lin-addr wp smep nxe r-w-x cpl x86-2)))
             (equal (mv-nth
                     1
                     (ia32e-la-to-pa-PD
                      lin-addr wp smep nxe r-w-x cpl x86-1))
                    (mv-nth
                     1
                     (ia32e-la-to-pa-PD
                      lin-addr wp smep nxe r-w-x cpl x86-2)))))
   :hints (("Goal"
            :in-theory (e/d* (ia32e-la-to-pa-page-directory
                              entry-found-p-and-lin-addr)
                             (not
                              xlate-equiv-x86s
                              bitops::logand-with-negated-bitmask
                              unsigned-byte-p
                              signed-byte-p
                              bitops::logior-equal-0))
            :use ((:instance xlate-equiv-entries-and-page-user-supervisor
                             (e-1 (mv-nth 2 (read-page-directory-entry lin-addr x86-1)))
                             (e-2 (mv-nth 2 (read-page-directory-entry lin-addr x86-2))))
                  (:instance xlate-equiv-entries-and-page-size
                             (e-1 (mv-nth 2 (read-page-directory-entry lin-addr x86-1)))
                             (e-2 (mv-nth 2 (read-page-directory-entry lin-addr x86-2)))))))))

(defthm mv-nth-0-ia32e-la-to-pa-PD-with-xlate-equiv-x86s
  (implies (xlate-equiv-x86s x86-1 x86-2)
           (equal (mv-nth
                   0
                   (ia32e-la-to-pa-PD
                    lin-addr wp smep nxe r-w-x cpl x86-1))
                  (mv-nth
                   0
                   (ia32e-la-to-pa-PD
                    lin-addr wp smep nxe r-w-x cpl x86-2))))
  :hints (("Goal"
           :in-theory (e/d* ()
                            (ia32e-la-to-pa-PD
                             n52p-mv-nth-1-page-directory-base-addr
                             n64p-rm-low-64-paging-entry
                             page-directory-entry-addr-is-in-gather-all-paging-structure-qword-addresses))
           :use ((:instance ia32e-la-to-pa-PD-with-xlate-equiv-x86s-2M-pages)
                 (:instance ia32e-la-to-pa-PD-with-xlate-equiv-x86s-4K-pages))))
  :rule-classes :congruence)

(defthm mv-nth-1-ia32e-la-to-pa-PD-with-xlate-equiv-x86s
  (implies (xlate-equiv-x86s x86-1 x86-2)
           (equal (mv-nth
                   1
                   (ia32e-la-to-pa-PD
                    lin-addr wp smep nxe r-w-x cpl x86-1))
                  (mv-nth
                   1
                   (ia32e-la-to-pa-PD
                    lin-addr wp smep nxe r-w-x cpl x86-2))))
  :hints (("Goal"
           :in-theory (e/d* ()
                            (ia32e-la-to-pa-PD
                             n52p-mv-nth-1-page-directory-base-addr
                             n64p-rm-low-64-paging-entry
                             page-directory-entry-addr-is-in-gather-all-paging-structure-qword-addresses))
           :use ((:instance ia32e-la-to-pa-PD-with-xlate-equiv-x86s-2M-pages)
                 (:instance ia32e-la-to-pa-PD-with-xlate-equiv-x86s-4K-pages))))
  :rule-classes :congruence)

(local (in-theory (e/d* (gather-all-paging-structure-qword-addresses-with-xlate-equiv-x86s
                         xlate-equiv-x86s-and-xlate-equiv-entries-at-qword-addresses?
                         xlate-equiv-entries-at-qword-addresses?-with-wm-low-64-with-different-x86)
                        ())))

(defthm xlate-equiv-x86s-with-mv-nth-2-ia32e-la-to-pa-PD
  (xlate-equiv-x86s
   (mv-nth 2 (ia32e-la-to-pa-PD lin-addr wp smep nxe r-w-x cpl x86))
   x86)
  :hints (("Goal"
           :in-theory (e/d* (ia32e-la-to-pa-page-directory-alt
                             good-paging-structures-x86p
                             read-page-directory-entry)
                            (bitops::logand-with-negated-bitmask
                             not
                             entry-found-p-and-good-paging-structures-x86p
                             no-duplicates-list-p
                             gather-all-paging-structure-qword-addresses-wm-low-64-different-x86))
           :use ((:instance entry-found-p-and-good-paging-structures-x86p)
                 (:instance gather-all-paging-structure-qword-addresses-wm-low-64-different-x86
                            (x86-equiv (mv-nth
                                        2
                                        (ia32e-la-to-pa-PT
                                         lin-addr
                                         (page-user-supervisor
                                          (mv-nth 2 (read-page-directory-entry lin-addr x86)))
                                         wp smep nxe r-w-x cpl x86)))
                            (index (page-directory-entry-addr
                                    lin-addr
                                    (mv-nth 1 (page-directory-base-addr lin-addr x86))))
                            (val (set-accessed-bit
                                  (mv-nth 2 (read-page-directory-entry lin-addr x86))))
                            (addrs (gather-all-paging-structure-qword-addresses x86))
                            (x86 x86))))))


(defthm two-page-table-walks-ia32e-la-to-pa-PD
  (and

   (equal
    (mv-nth
     0
     (ia32e-la-to-pa-PD
      lin-addr-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
      (mv-nth
       2
       (ia32e-la-to-pa-PD
        lin-addr-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
    (mv-nth
     0
     (ia32e-la-to-pa-PD
      lin-addr-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)))

   (equal
    (mv-nth
     1
     (ia32e-la-to-pa-PD
      lin-addr-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
      (mv-nth
       2
       (ia32e-la-to-pa-PD
        lin-addr-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
    (mv-nth
     1
     (ia32e-la-to-pa-PD
      lin-addr-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86))))

  :hints (("Goal" :in-theory (e/d* () (ia32e-la-to-pa-PD)))))

(local (in-theory (e/d* ()
                        (gather-all-paging-structure-qword-addresses-with-xlate-equiv-x86s
                         xlate-equiv-x86s-and-xlate-equiv-entries-at-qword-addresses?
                         xlate-equiv-entries-at-qword-addresses?-with-wm-low-64-with-different-x86))))

(in-theory (e/d* () (ia32e-la-to-pa-PD)))

;; ======================================================================

;; The following come in useful when reasoning about higher paging
;; structure traversals...

(defthm gather-all-paging-structure-qword-addresses-mv-nth-2-ia32e-la-to-pa-PD
  (implies (good-paging-structures-x86p x86)
           (equal (gather-all-paging-structure-qword-addresses
                   (mv-nth 2 (ia32e-la-to-pa-PD lin-addr wp smep nxe r-w-x cpl x86)))
                  (gather-all-paging-structure-qword-addresses x86)))
  :hints (("Goal"
           :use ((:instance
                  gather-all-paging-structure-qword-addresses-with-xlate-equiv-x86s
                  (x86-equiv (mv-nth 2 (ia32e-la-to-pa-PD lin-addr wp smep nxe r-w-x cpl x86))))))))

(defthm xlate-equiv-entries-at-qword-addresses?-mv-nth-2-ia32e-la-to-pa-PD
  (implies (and (equal addrs (gather-all-paging-structure-qword-addresses x86))
                (good-paging-structures-x86p x86))
           (equal (xlate-equiv-entries-at-qword-addresses?
                   addrs addrs
                   x86
                   (mv-nth 2 (ia32e-la-to-pa-PD lin-addr wp smep nxe r-w-x cpl x86)))
                  (xlate-equiv-entries-at-qword-addresses? addrs addrs x86 x86)))
  :hints (("Goal"
           :use ((:instance xlate-equiv-x86s-and-xlate-equiv-entries-at-qword-addresses?
                            (addrs addrs)
                            (x86 x86)
                            (x86-equiv
                             (mv-nth 2 (ia32e-la-to-pa-PD lin-addr wp smep nxe r-w-x cpl x86))))))))

;; ======================================================================
