;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")
(include-book "paging-page-table-lemmas" :ttags :all)

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))
(local (include-book "centaur/gl/gl" :dir :system))

(local (in-theory (e/d (entry-found-p-and-lin-addr
                        entry-found-p-and-good-paging-structures-x86p)
                       (unsigned-byte-p
                        signed-byte-p))))

;; ======================================================================

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

(local
 (def-gl-thm logand-loghead-and-page-directory-base-addr-helper
   :hyp (unsigned-byte-p 64 x)
   :concl (equal (logand 18446744073709547520 (ash (loghead 40 (logtail 12 x)) 12))
                 (ash (loghead 40 (logtail 12 x)) 12))
   :g-bindings `((x (:g-number ,(gl-int 0 1 65))))))

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

(defthmd paging-entry-no-page-fault-p-with-xlate-equiv-x86s-and-page-directory-entry-addr
  (implies (and
            (equal e-1
                   (rm-low-64
                    (page-directory-entry-addr
                     lin-addr
                     (mv-nth 1 (page-directory-base-addr lin-addr x86-1)))
                    x86-1))
            (equal e-2
                   (rm-low-64
                    (page-directory-entry-addr
                     lin-addr
                     (mv-nth 1 (page-directory-base-addr lin-addr x86-2)))
                    x86-2))
            (xlate-equiv-x86s x86-1 x86-2)
            (page-directory-entry-addr-found-p lin-addr x86-1))
           (and
            (equal (mv-nth
                    0
                    (paging-entry-no-page-fault-p
                     lin-addr e-1 wp smep nxe r-w-x cpl x86-1))
                   (mv-nth
                    0
                    (paging-entry-no-page-fault-p
                     lin-addr e-2 wp smep nxe r-w-x cpl x86-2)))
            (equal (mv-nth
                    1
                    (paging-entry-no-page-fault-p
                     lin-addr e-1 wp smep nxe r-w-x cpl x86-1))
                   (mv-nth
                    1
                    (paging-entry-no-page-fault-p
                     lin-addr e-2 wp smep nxe r-w-x cpl x86-2)))))
  :hints (("Goal"
           :in-theory (e/d* (paging-entry-no-page-fault-p
                             page-fault-exception)
                            (xlate-equiv-x86s
                             xlate-equiv-x86s-and-page-directory-entry-addr-value
                             xlate-equiv-x86s-and-page-directory-base-addr-address
                             xlate-equiv-x86s-and-page-directory-entry-addr-address
                             page-directory-entry-addr-found-p-and-xlate-equiv-x86s
                             bitops::logand-with-negated-bitmask
                             bitops::logior-equal-0
                             not))
           :use ((:instance xlate-equiv-x86s-and-page-directory-entry-addr-value)
                 (:instance xlate-equiv-x86s-and-page-directory-base-addr-address)
                 (:instance xlate-equiv-entries-and-page-present
                            (e1 (rm-low-64
                                 (page-directory-entry-addr
                                  lin-addr
                                  (mv-nth 1 (page-directory-base-addr lin-addr x86-1)))
                                 x86-1))
                            (e2 (rm-low-64
                                 (page-directory-entry-addr
                                  lin-addr
                                  (mv-nth 1 (page-directory-base-addr lin-addr x86-2)))
                                 x86-2)))
                 (:instance xlate-equiv-entries-and-page-size
                            (e1 (rm-low-64
                                 (page-directory-entry-addr
                                  lin-addr
                                  (mv-nth 1 (page-directory-base-addr lin-addr x86-1)))
                                 x86-1))
                            (e2 (rm-low-64
                                 (page-directory-entry-addr
                                  lin-addr
                                  (mv-nth 1 (page-directory-base-addr lin-addr x86-2)))
                                 x86-2)))
                 (:instance xlate-equiv-entries-and-page-read-write
                            (e1 (rm-low-64
                                 (page-directory-entry-addr
                                  lin-addr
                                  (mv-nth 1 (page-directory-base-addr lin-addr x86-1)))
                                 x86-1))
                            (e2 (rm-low-64
                                 (page-directory-entry-addr
                                  lin-addr
                                  (mv-nth 1 (page-directory-base-addr lin-addr x86-2)))
                                 x86-2)))
                 (:instance xlate-equiv-entries-and-page-user-supervisor
                            (e1 (rm-low-64
                                 (page-directory-entry-addr
                                  lin-addr
                                  (mv-nth 1 (page-directory-base-addr lin-addr x86-1)))
                                 x86-1))
                            (e2 (rm-low-64
                                 (page-directory-entry-addr
                                  lin-addr
                                  (mv-nth 1 (page-directory-base-addr lin-addr x86-2)))
                                 x86-2)))
                 (:instance xlate-equiv-entries-and-page-execute-disable
                            (e1 (rm-low-64
                                 (page-directory-entry-addr
                                  lin-addr
                                  (mv-nth 1 (page-directory-base-addr lin-addr x86-1)))
                                 x86-1))
                            (e2 (rm-low-64
                                 (page-directory-entry-addr
                                  lin-addr
                                  (mv-nth 1 (page-directory-base-addr lin-addr x86-2)))
                                 x86-2)))
                 (:instance xlate-equiv-entries-and-logtail
                            (e1 (rm-low-64
                                 (page-directory-entry-addr
                                  lin-addr
                                  (mv-nth 1 (page-directory-base-addr lin-addr x86-1)))
                                 x86-1))
                            (e2 (rm-low-64
                                 (page-directory-entry-addr
                                  lin-addr
                                  (mv-nth 1 (page-directory-base-addr lin-addr x86-2)))
                                 x86-2))
                            (n 13))
                 (:instance xlate-equiv-entries-and-logtail
                            (e1 (rm-low-64
                                 (page-directory-entry-addr
                                  lin-addr
                                  (mv-nth 1 (page-directory-base-addr lin-addr x86-1)))
                                 x86-1))
                            (e2 (rm-low-64
                                 (page-directory-entry-addr
                                  lin-addr
                                  (mv-nth 1 (page-directory-base-addr lin-addr x86-2)))
                                 x86-2))
                            (n 52))))))

(local
 (defthmd ia32e-la-to-pa-PD-with-xlate-equiv-x86s-2M-pages
   (implies (and (xlate-equiv-x86s x86-1 x86-2)
                 (equal
                  (page-size
                   (rm-low-64
                    (page-directory-entry-addr
                     lin-addr
                     (mv-nth 1 (page-directory-base-addr lin-addr x86-1)))
                    x86-1))
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
            :in-theory (e/d* (ia32e-la-to-pa-page-directory
                              entry-found-p-and-lin-addr)
                             (pml4-table-entry-addr-found-p-and-xlate-equiv-x86s
                              xlate-equiv-x86s
                              xlate-equiv-x86s-and-page-table-entry-addr-address
                              page-table-entry-addr-found-p-and-xlate-equiv-x86s
                              ia32e-la-to-pa-PT-with-xlate-equiv-x86s
                              xlate-equiv-x86s-and-page-directory-entry-addr-value
                              xlate-equiv-x86s-and-page-directory-base-addr-address
                              xlate-equiv-x86s-and-page-directory-entry-addr-address
                              xlate-equiv-x86s-and-page-table-base-addr-address
                              page-directory-entry-addr-found-p-and-xlate-equiv-x86s
                              bitops::logand-with-negated-bitmask
                              bitops::logior-equal-0))
            :use ((:instance paging-entry-no-page-fault-p-with-xlate-equiv-x86s-and-page-directory-entry-addr
                             (x86-1 x86-1)
                             (x86-2 x86-2)
                             (e-1
                              (rm-low-64
                               (page-directory-entry-addr
                                lin-addr
                                (mv-nth 1 (page-directory-base-addr lin-addr x86-1)))
                               x86-1))
                             (e-2
                              (rm-low-64
                               (page-directory-entry-addr
                                lin-addr
                                (mv-nth 1 (page-directory-base-addr lin-addr x86-2)))
                               x86-2)))
                  (:instance xlate-equiv-x86s-and-page-directory-entry-addr-value)
                  (:instance xlate-equiv-x86s-and-page-directory-base-addr-address)
                  (:instance page-directory-entry-addr-found-p-and-xlate-equiv-x86s)
                  (:instance page-directory-entry-addr-found-p-and-xlate-equiv-x86s
                             (x86-1 x86-2)
                             (x86-2 x86-1))
                  (:instance xlate-equiv-entries-and-logtail
                             (e1 (rm-low-64
                                  (page-directory-entry-addr
                                   lin-addr
                                   (mv-nth 1 (page-directory-base-addr lin-addr x86-2)))
                                  x86-1))
                             (e2 (rm-low-64
                                  (page-directory-entry-addr
                                   lin-addr
                                   (mv-nth 1 (page-directory-base-addr lin-addr x86-2)))
                                  x86-2))
                             (n 21))
                  (:instance xlate-equiv-entries-and-page-size
                             (e1 (rm-low-64
                                  (page-directory-entry-addr
                                   lin-addr
                                   (mv-nth 1 (page-directory-base-addr lin-addr x86-1)))
                                  x86-1))
                             (e2 (rm-low-64
                                  (page-directory-entry-addr
                                   lin-addr
                                   (mv-nth 1 (page-directory-base-addr lin-addr x86-2)))
                                  x86-2))))))))

(local
 (defthmd ia32e-la-to-pa-PD-with-xlate-equiv-x86s-4K-pages
   (implies (and (xlate-equiv-x86s x86-1 x86-2)
                 (equal
                  (page-size
                   (rm-low-64
                    (page-directory-entry-addr
                     lin-addr
                     (mv-nth 1 (page-directory-base-addr lin-addr x86-1)))
                    x86-1))
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
                             (pml4-table-entry-addr-found-p-and-xlate-equiv-x86s
                              not
                              xlate-equiv-x86s
                              xlate-equiv-x86s-and-page-table-entry-addr-address
                              page-table-entry-addr-found-p-and-xlate-equiv-x86s
                              xlate-equiv-x86s-and-page-directory-entry-addr-value
                              xlate-equiv-x86s-and-page-directory-base-addr-address
                              xlate-equiv-x86s-and-page-directory-entry-addr-address
                              xlate-equiv-x86s-and-page-table-base-addr-address
                              page-directory-entry-addr-found-p-and-xlate-equiv-x86s
                              bitops::logand-with-negated-bitmask
                              unsigned-byte-p
                              signed-byte-p
                              bitops::logior-equal-0))
            :use ((:instance paging-entry-no-page-fault-p-with-xlate-equiv-x86s-and-page-directory-entry-addr
                             (x86-1 x86-1)
                             (x86-2 x86-2)
                             (e-1
                              (rm-low-64
                               (page-directory-entry-addr
                                lin-addr
                                (mv-nth 1 (page-directory-base-addr lin-addr x86-1)))
                               x86-1))
                             (e-2
                              (rm-low-64
                               (page-directory-entry-addr
                                lin-addr
                                (mv-nth 1 (page-directory-base-addr lin-addr x86-2)))
                               x86-2)))
                  (:instance xlate-equiv-entries-and-page-user-supervisor
                             (e1 (rm-low-64
                                  (page-directory-entry-addr
                                   lin-addr
                                   (mv-nth 1 (page-directory-base-addr lin-addr x86-1)))
                                  x86-1))
                             (e2 (rm-low-64
                                  (page-directory-entry-addr
                                   lin-addr
                                   (mv-nth 1 (page-directory-base-addr lin-addr x86-2)))
                                  x86-2)))
                  (:instance xlate-equiv-entries-and-page-size
                             (e1 (rm-low-64
                                  (page-directory-entry-addr
                                   lin-addr
                                   (mv-nth 1 (page-directory-base-addr lin-addr x86-1)))
                                  x86-1))
                             (e2 (rm-low-64
                                  (page-directory-entry-addr
                                   lin-addr
                                   (mv-nth 1 (page-directory-base-addr lin-addr x86-2)))
                                  x86-2)))
                  (:instance xlate-equiv-x86s-and-page-directory-entry-addr-value)
                  (:instance xlate-equiv-x86s-and-page-directory-base-addr-address)
                  (:instance page-directory-entry-addr-found-p-and-xlate-equiv-x86s)
                  (:instance page-directory-entry-addr-found-p-and-xlate-equiv-x86s
                             (x86-1 x86-2)
                             (x86-2 x86-1)))))))

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
           :use ((:instance entry-found-p-and-good-paging-structures-x86p)
                 (:instance gather-all-paging-structure-qword-addresses-wm-low-64-different-x86
                            (x86-equiv (mv-nth
                                        2
                                        (ia32e-la-to-pa-PT
                                         lin-addr
                                         (page-user-supervisor
                                          (rm-low-64 (page-directory-entry-addr
                                                      lin-addr
                                                      (mv-nth 1
                                                              (page-directory-base-addr lin-addr x86)))
                                                     x86))
                                         wp smep nxe r-w-x cpl x86)))
                            (index (page-directory-entry-addr
                                    lin-addr
                                    (mv-nth 1 (page-directory-base-addr lin-addr x86))))
                            (val (set-accessed-bit
                                  (rm-low-64 (page-directory-entry-addr
                                              lin-addr
                                              (mv-nth 1 (page-directory-base-addr lin-addr x86)))
                                             x86)))
                            (addrs (gather-all-paging-structure-qword-addresses x86))
                            (x86 x86)))
           :in-theory (e/d* (ia32e-la-to-pa-page-directory
                             good-paging-structures-x86p)
                            (bitops::logand-with-negated-bitmask
                             not
                             entry-found-p-and-good-paging-structures-x86p
                             xlate-equiv-x86s-and-page-table-entry-addr-address
                             xlate-equiv-x86s-and-page-table-base-addr-address
                             no-duplicates-list-p
                             gather-all-paging-structure-qword-addresses-wm-low-64-different-x86)))))


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

;; *-entry-addr-found-p and ia32e-la-to-pa-PD:

(defthm page-table-entry-addr-found-p-after-a-page-directory-walk
  (implies (and (page-table-entry-addr-found-p lin-addr-1 x86)
                (page-table-entry-addr-found-p lin-addr-2 x86))
           (page-table-entry-addr-found-p
            lin-addr-1
            (mv-nth 2
                    (ia32e-la-to-pa-PD
                     lin-addr-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
  :hints (("Goal"
           :use ((:instance page-table-entry-addr-found-p-and-xlate-equiv-x86s
                            (x86-1 x86)
                            (lin-addr lin-addr-1)
                            (x86-2
                             (mv-nth 2
                                     (ia32e-la-to-pa-PD
                                      lin-addr-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
                 (:instance xlate-equiv-x86s-with-mv-nth-2-ia32e-la-to-pa-PD
                            (x86 x86)
                            (lin-addr lin-addr-2)
                            (wp wp-2)
                            (smep smep-2)
                            (nxe nxe-2)
                            (r-w-x r-w-x-2)
                            (cpl cpl-2)))
           :in-theory (e/d* ()
                            (physical-address-p
                             page-table-entry-addr-found-p-and-xlate-equiv-x86s
                             xlate-equiv-x86s-with-mv-nth-2-ia32e-la-to-pa-PD
                             xlate-equiv-x86s-and-page-dir-ptr-table-base-addr-address
                             xlate-equiv-x86s-and-page-dir-ptr-table-entry-addr-address
                             xlate-equiv-x86s-and-page-directory-base-addr-address
                             xlate-equiv-x86s-and-page-directory-base-addr-error
                             xlate-equiv-x86s-and-page-directory-entry-addr-address
                             xlate-equiv-x86s-and-page-table-base-addr-address
                             xlate-equiv-x86s-and-page-table-entry-addr-address
                             bitops::logand-with-negated-bitmask)))))

(defthm page-directory-entry-addr-found-p-after-a-page-directory-walk
  (implies (and (page-directory-entry-addr-found-p lin-addr-1 x86)
                (page-directory-entry-addr-found-p lin-addr-2 x86))
           (page-directory-entry-addr-found-p
            lin-addr-1
            (mv-nth 2
                    (ia32e-la-to-pa-PD
                     lin-addr-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
  :hints (("Goal"
           :use ((:instance page-directory-entry-addr-found-p-and-xlate-equiv-x86s
                            (x86-1 x86)
                            (lin-addr lin-addr-1)
                            (x86-2
                             (mv-nth 2
                                     (ia32e-la-to-pa-PD
                                      lin-addr-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
                 (:instance xlate-equiv-x86s-with-mv-nth-2-ia32e-la-to-pa-PD
                            (x86 x86)
                            (lin-addr lin-addr-2)
                            (wp wp-2)
                            (smep smep-2)
                            (nxe nxe-2)
                            (r-w-x r-w-x-2)
                            (cpl cpl-2)))
           :in-theory (e/d* ()
                            (physical-address-p
                             page-directory-entry-addr-found-p-and-xlate-equiv-x86s
                             xlate-equiv-x86s-with-mv-nth-2-ia32e-la-to-pa-PD
                             xlate-equiv-x86s-and-page-dir-ptr-table-base-addr-address
                             xlate-equiv-x86s-and-page-dir-ptr-table-entry-addr-address
                             xlate-equiv-x86s-and-page-directory-base-addr-address
                             xlate-equiv-x86s-and-page-directory-base-addr-error
                             xlate-equiv-x86s-and-page-directory-entry-addr-address
                             xlate-equiv-x86s-and-page-table-base-addr-address
                             xlate-equiv-x86s-and-page-table-entry-addr-address
                             bitops::logand-with-negated-bitmask)))))

(defthm page-dir-ptr-table-entry-addr-found-p-after-a-page-directory-walk
  (implies (and (page-dir-ptr-table-entry-addr-found-p lin-addr-1 x86)
                (page-dir-ptr-table-entry-addr-found-p lin-addr-2 x86))
           (page-dir-ptr-table-entry-addr-found-p
            lin-addr-1
            (mv-nth 2
                    (ia32e-la-to-pa-PD
                     lin-addr-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
  :hints (("Goal"
           :use ((:instance page-dir-ptr-table-entry-addr-found-p-and-xlate-equiv-x86s
                            (x86-1 x86)
                            (lin-addr lin-addr-1)
                            (x86-2
                             (mv-nth 2
                                     (ia32e-la-to-pa-PD
                                      lin-addr-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
                 (:instance xlate-equiv-x86s-with-mv-nth-2-ia32e-la-to-pa-PD
                            (x86 x86)
                            (lin-addr lin-addr-2)
                            (wp wp-2)
                            (smep smep-2)
                            (nxe nxe-2)
                            (r-w-x r-w-x-2)
                            (cpl cpl-2)))
           :in-theory (e/d* ()
                            (physical-address-p
                             page-dir-ptr-table-entry-addr-found-p-and-xlate-equiv-x86s
                             xlate-equiv-x86s-with-mv-nth-2-ia32e-la-to-pa-PD
                             xlate-equiv-x86s-and-page-dir-ptr-table-base-addr-address
                             xlate-equiv-x86s-and-page-dir-ptr-table-entry-addr-address
                             xlate-equiv-x86s-and-page-dir-ptr-table-base-addr-address
                             xlate-equiv-x86s-and-page-dir-ptr-table-entry-addr-address
                             xlate-equiv-x86s-and-page-table-base-addr-address
                             xlate-equiv-x86s-and-page-table-entry-addr-address
                             bitops::logand-with-negated-bitmask)))))

(defthm pml4-table-entry-addr-found-p-after-a-page-directory-walk
  (implies (and (pml4-table-entry-addr-found-p lin-addr-1 x86)
                (pml4-table-entry-addr-found-p lin-addr-2 x86))
           (pml4-table-entry-addr-found-p
            lin-addr-1
            (mv-nth 2
                    (ia32e-la-to-pa-PD
                     lin-addr-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
  :hints (("Goal"
           :use ((:instance pml4-table-entry-addr-found-p-and-xlate-equiv-x86s
                            (x86-1 x86)
                            (lin-addr lin-addr-1)
                            (x86-2
                             (mv-nth 2
                                     (ia32e-la-to-pa-PD
                                      lin-addr-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
                 (:instance xlate-equiv-x86s-with-mv-nth-2-ia32e-la-to-pa-PD
                            (x86 x86)
                            (lin-addr lin-addr-2)
                            (wp wp-2)
                            (smep smep-2)
                            (nxe nxe-2)
                            (r-w-x r-w-x-2)
                            (cpl cpl-2)))
           :in-theory (e/d* ()
                            (physical-address-p
                             pml4-table-entry-addr-found-p-and-xlate-equiv-x86s
                             xlate-equiv-x86s-with-mv-nth-2-ia32e-la-to-pa-PD
                             xlate-equiv-x86s-and-pml4-table-base-addr-address
                             xlate-equiv-x86s-and-pml4-table-entry-addr-address
                             xlate-equiv-x86s-and-pml4-table-base-addr-address
                             xlate-equiv-x86s-and-pml4-table-entry-addr-address
                             xlate-equiv-x86s-and-page-table-base-addr-address
                             xlate-equiv-x86s-and-page-table-entry-addr-address
                             bitops::logand-with-negated-bitmask)))))

;; ======================================================================
