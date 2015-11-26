;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")
(include-book "paging-page-table-lemmas" :ttags :all)

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))
(local (include-book "centaur/gl/gl" :dir :system))

(local (in-theory (e/d (entry-found-p-and-lin-addr
                        entry-found-p-and-good-paging-structures-x86p)
                       ())))

;; ======================================================================

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

(local
 (defthmd ia32e-la-to-pa-PD-with-xlate-equiv-x86s-2M-pages
   ;; TO-DO: Speed this up.
   (implies (and (xlate-equiv-x86s x86-1 x86-2)
                 (logbitp
                  7
                  (rm-low-64
                   (page-directory-entry-addr
                    lin-addr
                    (mv-nth 1 (page-directory-base-addr lin-addr x86-1)))
                   x86-1)))
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
                              entry-found-p-and-lin-addr
                              PAGING-ENTRY-NO-PAGE-FAULT-P
                              PAGE-FAULT-EXCEPTION)
                             (xlate-equiv-x86s
                              xlate-equiv-x86s-and-page-table-entry-addr-address
                              page-table-entry-addr-found-p-and-xlate-equiv-x86s
                              ia32e-la-to-pa-PT-with-xlate-equiv-x86s
                              xlate-equiv-x86s-and-page-directory-entry-addr-value
                              xlate-equiv-x86s-and-page-directory-base-addr-address
                              xlate-equiv-x86s-and-page-directory-entry-addr-address
                              xlate-equiv-x86s-and-page-table-base-addr-address
                              page-directory-entry-addr-found-p-and-xlate-equiv-x86s
                              bitops::logand-with-negated-bitmask
                              unsigned-byte-p
                              signed-byte-p
                              bitops::logior-equal-0))
            :use ((:instance xlate-equiv-x86s-and-page-directory-entry-addr-value)
                  (:instance xlate-equiv-x86s-and-page-directory-base-addr-address)
                  (:instance page-directory-entry-addr-found-p-and-xlate-equiv-x86s)
                  (:instance page-directory-entry-addr-found-p-and-xlate-equiv-x86s
                             (x86-1 x86-2)
                             (x86-2 x86-1))
                  (:instance xlate-equiv-entries-open
                             (e1 (rm-low-64
                                  (page-directory-entry-addr
                                   lin-addr
                                   (mv-nth 1 (page-directory-base-addr lin-addr x86-2)))
                                  x86-1))
                             (e2 (rm-low-64
                                  (page-directory-entry-addr
                                   lin-addr
                                   (mv-nth 1 (page-directory-base-addr lin-addr x86-2)))
                                  x86-2)))
                  ;; (:instance page-table-entry-addr-found-p-and-xlate-equiv-x86s)
                  ;; xlate-equiv-entries-and-loghead
                  (:instance xlate-equiv-entries-and-loghead
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
                             (n 1))
                  ;; xlate-equiv-entries-and-logtail
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
                             (n 13))
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
                             (n 52))
                  ;; loghead-smaller-and-logbitp
                  (:instance loghead-smaller-and-logbitp
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
                             (m 1)
                             (n 5))
                  (:instance loghead-smaller-and-logbitp
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
                             (m 2)
                             (n 5))
                  ;; logtail-bigger-and-logbitp
                  (:instance logtail-bigger-and-logbitp
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
                             (m 7)
                             (n 7))
                  (:instance logtail-bigger-and-logbitp
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
                             (m 7)
                             (n 52))
                  (:instance logtail-bigger-and-logbitp
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
                             (m 7)
                             (n 63)))))))

(local
 (defthmd ia32e-la-to-pa-PD-with-xlate-equiv-x86s-4K-pages
   ;; TO-DO: Speed this up.
   (implies (and (xlate-equiv-x86s x86-1 x86-2)
                 (not
                  (logbitp
                   7
                   (rm-low-64
                    (page-directory-entry-addr
                     lin-addr
                     (mv-nth 1 (page-directory-base-addr lin-addr x86-1)))
                    x86-1))))
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
                              entry-found-p-and-lin-addr
                              PAGING-ENTRY-NO-PAGE-FAULT-P
                              PAGE-FAULT-EXCEPTION)
                             (xlate-equiv-x86s
                              xlate-equiv-x86s-and-page-table-entry-addr-address
                              page-table-entry-addr-found-p-and-xlate-equiv-x86s
                              ia32e-la-to-pa-PT-with-xlate-equiv-x86s
                              xlate-equiv-x86s-and-page-directory-entry-addr-value
                              xlate-equiv-x86s-and-page-directory-base-addr-address
                              xlate-equiv-x86s-and-page-directory-entry-addr-address
                              xlate-equiv-x86s-and-page-table-base-addr-address
                              page-directory-entry-addr-found-p-and-xlate-equiv-x86s
                              bitops::logand-with-negated-bitmask
                              unsigned-byte-p
                              signed-byte-p
                              bitops::logior-equal-0))
            :use ((:instance xlate-equiv-x86s-and-page-directory-entry-addr-value)
                  (:instance xlate-equiv-x86s-and-page-directory-base-addr-address)
                  (:instance page-directory-entry-addr-found-p-and-xlate-equiv-x86s)
                  (:instance page-directory-entry-addr-found-p-and-xlate-equiv-x86s
                             (x86-1 x86-2)
                             (x86-2 x86-1))
                  ;; (:instance page-table-entry-addr-found-p-and-xlate-equiv-x86s)
                  (:instance xlate-equiv-entries-open
                             (e1 (rm-low-64
                                  (page-directory-entry-addr
                                   lin-addr
                                   (mv-nth 1 (page-directory-base-addr lin-addr x86-2)))
                                  x86-1))
                             (e2 (rm-low-64
                                  (page-directory-entry-addr
                                   lin-addr
                                   (mv-nth 1 (page-directory-base-addr lin-addr x86-2)))
                                  x86-2)))
                  ;; xlate-equiv-entries-and-loghead
                  (:instance xlate-equiv-entries-and-loghead
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
                             (n 1))
                  ;; xlate-equiv-entries-and-logtail
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
                             (n 13))
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
                             (n 52))
                  ;; loghead-smaller-and-logbitp
                  (:instance loghead-smaller-and-logbitp
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
                             (m 1)
                             (n 5))
                  (:instance loghead-smaller-and-logbitp
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
                             (m 2)
                             (n 5))
                  ;; logtail-bigger-and-logbitp
                  (:instance logtail-bigger-and-logbitp
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
                             (m 7)
                             (n 7))
                  (:instance logtail-bigger-and-logbitp
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
                             (m 7)
                             (n 52))
                  (:instance logtail-bigger-and-logbitp
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
                             (m 7)
                             (n 63)))))))


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
           :use ((:instance ia32e-la-to-pa-PD-with-xlate-equiv-x86s-2M-pages)
                 (:instance ia32e-la-to-pa-PD-with-xlate-equiv-x86s-4K-pages))))
  :rule-classes :congruence)

;; (i-am-here)

(defthm gather-all-paging-structure-qword-addresses-mv-nth-2-ia32e-la-to-pa-PT
  (implies (page-directory-entry-addr-found-p lin-addr x86)
           (equal (gather-all-paging-structure-qword-addresses
                   (mv-nth 2 (ia32e-la-to-pa-PT lin-addr u-s-acc wp smep nxe r-w-x cpl x86)))
                  (gather-all-paging-structure-qword-addresses x86)))
  :hints (("Goal"
           :use ((:instance entry-found-p-and-good-paging-structures-x86p))
           :in-theory (e/d* (page-table-entry-no-page-fault-p
                             good-paging-structures-x86p
                             entry-found-p-and-lin-addr
                             page-fault-exception
                             ia32e-la-to-pa-PT
                             ia32e-la-to-pa-page-table)
                            (bitops::logand-with-negated-bitmask
                             page-directory-entry-addr-found-p)))))

(i-am-here)

(defthm xlate-equiv-entries-at-qword-addresses?-paging-entry-no-page-fault-p-commuted
  (equal (xlate-equiv-entries-at-qword-addresses?
          addrs addrs
          (mv-nth 2 (paging-entry-no-page-fault-p
                     lin-addr entry wp smep nxe r-w-x cpl x86))
          x86)
         (xlate-equiv-entries-at-qword-addresses? addrs addrs x86 x86))
  :hints (("Goal"
           :use ((:instance xlate-equiv-entries-at-qword-addresses?-paging-entry-no-page-fault-p)
                 (:instance xlate-equiv-entries-at-qword-addresses?-commutative
                            (a addrs)
                            (b addrs)
                            (x x86)
                            (y (mv-nth 2 (paging-entry-no-page-fault-p
                                          lin-addr entry wp smep nxe r-w-x cpl x86)))))
           :in-theory (e/d* ()
                            (xlate-equiv-entries-at-qword-addresses?-paging-entry-no-page-fault-p
                             xlate-equiv-entries-at-qword-addresses?)))))

(defthm xlate-equiv-entries-at-qword-addresses?-page-table-entry-no-page-fault-p-commuted
  (equal
   (xlate-equiv-entries-at-qword-addresses?
    addrs addrs
    (mv-nth 2 (page-table-entry-no-page-fault-p
               lin-addr entry u-s-acc wp smep nxe r-w-x cpl x86))
    x86)
   (xlate-equiv-entries-at-qword-addresses? addrs addrs x86 x86))
  :hints (("Goal"
           :use ((:instance xlate-equiv-entries-at-qword-addresses?-page-table-entry-no-page-fault-p)
                 (:instance xlate-equiv-entries-at-qword-addresses?-commutative
                            (a addrs)
                            (b addrs)
                            (x x86)
                            (y (mv-nth 2 (page-table-entry-no-page-fault-p
                                          lin-addr entry u-s-acc wp smep nxe r-w-x cpl x86)))))
           :in-theory (e/d* ()
                            (xlate-equiv-entries-at-qword-addresses?-page-table-entry-no-page-fault-p
                             xlate-equiv-entries-at-qword-addresses?)))))

(defthm xlate-equiv-entries-at-qword-addresses?-mv-nth-2-ia32e-la-to-pa-PT
  (implies (and (good-paging-structures-x86p x86)
                (equal addrs (gather-all-paging-structure-qword-addresses x86)))
           (equal (xlate-equiv-entries-at-qword-addresses?
                   addrs addrs
                   x86
                   (mv-nth 2 (ia32e-la-to-pa-PT lin-addr u-s-acc wp smep nxe r-w-x cpl x86)))
                  (xlate-equiv-entries-at-qword-addresses? addrs addrs x86 x86)))
  :hints (("Goal"
           :use ((:instance xlate-equiv-entries-at-qword-addresses?-page-table-entry-no-page-fault-p
                            (entry
                             (rm-low-64
                              (page-table-entry-addr
                               lin-addr
                               (mv-nth 1 (page-table-base-addr lin-addr x86)))
                              x86))))
           :in-theory (e/d* (ia32e-la-to-pa-PT
                             ia32e-la-to-pa-page-table
                             good-paging-structures-x86p)
                            (bitops::logand-with-negated-bitmask
                             xlate-equiv-entries-at-qword-addresses?-page-table-entry-no-page-fault-p-commuted)))))

(defthm xlate-equiv-entries-at-qword-addresses?-mv-nth-2-ia32e-la-to-pa-PT-commuted
  (implies (and (good-paging-structures-x86p x86)
                (equal addrs (gather-all-paging-structure-qword-addresses x86)))
           (equal (xlate-equiv-entries-at-qword-addresses?
                   addrs addrs
                   (mv-nth 2 (ia32e-la-to-pa-PT lin-addr u-s-acc wp smep nxe r-w-x cpl x86))
                   x86)
                  (xlate-equiv-entries-at-qword-addresses? addrs addrs x86 x86)))
  :hints (("Goal"
           :use ((:instance xlate-equiv-entries-at-qword-addresses?-page-table-entry-no-page-fault-p-commuted
                            (entry
                             (rm-low-64
                              (page-table-entry-addr
                               lin-addr
                               (mv-nth 1 (page-table-base-addr lin-addr x86)))
                              x86))))
           :in-theory (e/d* (ia32e-la-to-pa-PT
                             ia32e-la-to-pa-page-table
                             good-paging-structures-x86p)
                            (bitops::logand-with-negated-bitmask
                             xlate-equiv-entries-at-qword-addresses?-page-table-entry-no-page-fault-p-commuted)))))

(defthm xlate-equiv-entries-at-qword-addresses?-with-wm-low-64-commuted
  (implies (and (mult-8-qword-paddr-list-listp addrs)
                (no-duplicates-list-p addrs)
                (member-list-p index addrs)
                (or (equal val (set-accessed-bit (rm-low-64 index x86)))
                    (equal val (set-dirty-bit (rm-low-64 index x86)))
                    (equal val (set-dirty-bit (set-accessed-bit (rm-low-64 index x86)))))
                (x86p x86))
           (equal
            (xlate-equiv-entries-at-qword-addresses?
             addrs addrs (wm-low-64 index val x86) x86)
            (xlate-equiv-entries-at-qword-addresses? addrs addrs x86 x86)))
  :hints (("Goal"
           :use ((:instance xlate-equiv-entries-at-qword-addresses?-with-wm-low-64)
                 (:instance xlate-equiv-entries-at-qword-addresses?-commutative
                            (a addrs)
                            (b addrs)
                            (x x86)
                            (y (wm-low-64 index val x86))))
           :in-theory (e/d* ()
                            (member-list-p
                             xlate-equiv-entries-at-qword-addresses?-with-wm-low-64
                             no-duplicates-list-p
                             member-p
                             physical-address-p)))))


;; (skip-proofs
;;  (defthm xlate-equiv-entries-at-qword-addresses?-wm-low-64-with-different-x86s
;;    ;; x86-2: Original x86
;;    ;; x86-1: E.g.: mv-nth-2-ia32e-la-to-pa-PT with x86
;;    (implies (and (mult-8-qword-paddr-list-listp addrs)
;;                  (no-duplicates-list-p addrs)
;;                  (member-list-p index addrs)
;;                  (equal val (set-accessed-bit (rm-low-64 index x86-2)))
;;                  ;; (or (equal val (set-accessed-bit (rm-low-64 index x86-2)))
;;                  ;;     (equal val (set-dirty-bit (rm-low-64 index x86-2)))
;;                  ;;     (equal val (set-dirty-bit (set-accessed-bit (rm-low-64 index x86-2)))))
;;                  (xlate-equiv-x86s x86-1 x86-2))
;;             (equal
;;              (xlate-equiv-entries-at-qword-addresses?
;;               addrs addrs
;;               x86-2
;;               (wm-low-64 index val x86-1))
;;              (xlate-equiv-entries-at-qword-addresses? addrs addrs x86-2 x86-1)))
;;    :hints (("Goal"
;;             :in-theory (e/d* (xlate-equiv-entries-at-qword-addresses?
;;                               xlate-equiv-entries-at-qword-addresses-aux?)
;;                              ())))))

;; (skip-proofs
;;  (defthm gather-all-paging-structure-qword-addresses-wm-low-64-mv-nth-2-ia32e-la-to-pa-PT
;;    (implies (and (page-directory-entry-addr-found-p lin-addr x86)
;;                  (mult-8-qword-paddr-list-listp (gather-all-paging-structure-qword-addresses x86))
;;                  (no-duplicates-list-p (gather-all-paging-structure-qword-addresses x86))
;;                  (x86p x86)
;;                  (equal index
;;                         (page-directory-entry-addr
;;                          lin-addr
;;                          (mv-nth 1 (page-directory-base-addr lin-addr x86))))
;;                  (equal val (set-accessed-bit (rm-low-64 index x86))))
;;             (equal (gather-all-paging-structure-qword-addresses
;;                     (wm-low-64
;;                      index val
;;                      (mv-nth 2 (ia32e-la-to-pa-PT lin-addr u-s-acc wp smep nxe r-w-x cpl x86))))
;;                    (gather-all-paging-structure-qword-addresses x86)))
;;    :hints (("Goal"
;;             :use ((:instance entry-found-p-and-good-paging-structures-x86p))
;;             :in-theory (e/d* (page-table-entry-no-page-fault-p
;;                               good-paging-structures-x86p
;;                               entry-found-p-and-lin-addr
;;                               page-fault-exception
;;                               ia32e-la-to-pa-PT
;;                               ia32e-la-to-pa-page-table)
;;                              (bitops::logand-with-negated-bitmask
;;                               page-directory-entry-addr-found-p))))))

(defthm gather-all-paging-structure-qword-addresses-with-xlate-equiv-x86s
  (implies (and (good-paging-structures-x86p x86)
                (xlate-equiv-x86s x86 x86-equiv))
           (equal (gather-all-paging-structure-qword-addresses x86-equiv)
                  (gather-all-paging-structure-qword-addresses x86)))
  :hints
  (("Goal" :in-theory (e/d* (gather-all-paging-structure-qword-addresses) ()))))

(defthm xlate-equiv-x86s-and-xlate-equiv-entries-at-qword-addresses?
  (implies (and (good-paging-structures-x86p x86)
                (xlate-equiv-x86s x86 x86-equiv)
                (equal addrs (gather-all-paging-structure-qword-addresses x86)))
           (xlate-equiv-entries-at-qword-addresses?
            addrs addrs x86 x86-equiv))
  :hints
  (("Goal" :in-theory (e/d* (xlate-equiv-entries-at-qword-addresses?
                             good-paging-structures-x86p)
                            ()))))


(defthm xlate-equiv-x86s-with-mv-nth-2-ia32e-la-to-pa-PD
  (xlate-equiv-x86s
   (mv-nth 2 (ia32e-la-to-pa-PD lin-addr wp smep nxe r-w-x cpl x86))
   x86)
  :hints (("Goal"
           :use ((:instance entry-found-p-and-good-paging-structures-x86p)
                 (:instance gather-all-paging-structure-qword-addresses-mv-nth-2-ia32e-la-to-pa-PT
                            (u-s-acc
                             (bool->bit
                              (logbitp
                               2
                               (rm-low-64 (page-directory-entry-addr
                                           lin-addr
                                           (mv-nth 1
                                                   (page-directory-base-addr lin-addr x86)))
                                          x86))))))
           :in-theory (e/d* (ia32e-la-to-pa-page-directory
                             entry-found-p-and-lin-addr
                             good-paging-structures-x86p)
                            (bitops::logand-with-negated-bitmask
                             entry-found-p-and-good-paging-structures-x86p
                             xlate-equiv-x86s-and-page-table-entry-addr-address
                             xlate-equiv-x86s-and-page-table-base-addr-address
                             no-duplicates-list-p
                             gather-all-paging-structure-qword-addresses-mv-nth-2-ia32e-la-to-pa-PT
                             gather-all-paging-structure-qword-addresses-with-xlate-equiv-x86s))))
  :otf-flg t)

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

(in-theory (e/d* () (ia32e-la-to-pa-PD)))

;; ======================================================================
