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

;; Start clean up here...

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

(defthm gather-qword-addresses-corresponding-to-1-entry-with-different-x86-entries
  (implies (and (xlate-equiv-entries (rm-low-64 addr x86-equiv)
                                     (rm-low-64 addr x86))
                (x86p x86)
                (x86p x86-equiv))
           (equal (gather-qword-addresses-corresponding-to-1-entry addr x86-equiv)
                  (gather-qword-addresses-corresponding-to-1-entry addr x86)))
  :hints (("Goal" :in-theory (e/d* (gather-qword-addresses-corresponding-to-1-entry)
                                   (unsigned-byte-p))
           :use ((:instance xlate-equiv-entries-and-loghead
                            (e1 (rm-low-64 addr x86-equiv))
                            (e2 (rm-low-64 addr x86))
                            (n 1))
                 (:instance logtail-bigger-and-logbitp
                            (e1 (rm-low-64 addr x86-equiv))
                            (e2 (rm-low-64 addr x86))
                            (n 7)
                            (m 7))
                 (:instance xlate-equiv-entries-and-logtail
                            (e1 (rm-low-64 addr x86-equiv))
                            (e2 (rm-low-64 addr x86))
                            (n 7))
                 (:instance xlate-equiv-entries-and-logtail
                            (e1 (rm-low-64 addr x86-equiv))
                            (e2 (rm-low-64 addr x86))
                            (n 12))))))

(defthm gather-qword-addresses-corresponding-to-1-entry-wm-low-64-with-different-x86-disjoint
  (implies (and (disjoint-p (addr-range 8 index) (addr-range 8 addr))
                (physical-address-p addr)
                (physical-address-p index)
                (equal (gather-qword-addresses-corresponding-to-1-entry addr x86-equiv)
                       (gather-qword-addresses-corresponding-to-1-entry addr x86)))
           ;; (xlate-equiv-entries (rm-low-64 addr x86-equiv)
           ;;                      (rm-low-64 addr x86))
           (equal (gather-qword-addresses-corresponding-to-1-entry
                   addr (wm-low-64 index val x86-equiv))
                  (gather-qword-addresses-corresponding-to-1-entry addr x86)))
  :hints (("Goal" :in-theory (e/d* (gather-qword-addresses-corresponding-to-1-entry)
                                   (gather-qword-addresses-corresponding-to-1-entry-wm-low-64
                                    unsigned-byte-p))
           :use ((:instance gather-qword-addresses-corresponding-to-1-entry-wm-low-64
                            (x86 x86-equiv))))))

(defthm gather-qword-addresses-corresponding-to-1-entry-wm-low-64-with-different-x86
  ;; This is a surprising theorem. Even if we write an
  ;; xlate-equiv-entries value to addr in x86-equiv (a state that may
  ;; be different from x86), there's no guarantee that the qword
  ;; addresses of the inferior structure entry pointed to by this new
  ;; value will be the same in x86 and x86-equiv. However, that's
  ;; exactly what this theorem says, and this is because of the way
  ;; gather-qword-addresses-corresponding-to-1-entry is defined ---
  ;; simply in terms of create-qword-address-list once the entry at
  ;; addr is read from the x86 (or x86-equiv) state.
  (implies (and (xlate-equiv-entries val (rm-low-64 addr x86))
                (unsigned-byte-p 64 val)
                (physical-address-p addr)
                (physical-address-p (+ 7 addr))
                (x86p x86))
           (equal (gather-qword-addresses-corresponding-to-1-entry
                   addr (wm-low-64 addr val x86-equiv))
                  (gather-qword-addresses-corresponding-to-1-entry addr x86)))
  :hints (("Goal" :in-theory (e/d* (gather-qword-addresses-corresponding-to-1-entry)
                                   ())
           :use ((:instance xlate-equiv-entries-and-loghead
                            (e1 val)
                            (e2 (rm-low-64 addr x86))
                            (n 1))
                 (:instance logtail-bigger-and-logbitp
                            (e1 val)
                            (e2 (rm-low-64 addr x86))
                            (n 7)
                            (m 7))
                 (:instance xlate-equiv-entries-and-logtail
                            (e1 val)
                            (e2 (rm-low-64 addr x86))
                            (n 7))
                 (:instance xlate-equiv-entries-and-logtail
                            (e1 val)
                            (e2 (rm-low-64 addr x86))
                            (n 12))))))

(defthm gather-qword-addresses-corresponding-to-entries-wm-low-64-with-different-x86-disjoint
  (implies (and (equal (gather-qword-addresses-corresponding-to-entries addrs x86-equiv)
                       (gather-qword-addresses-corresponding-to-entries addrs x86))
                (not (member-p index addrs))
                (equal (loghead 3 index) 0)
                (physical-address-p index)
                (mult-8-qword-paddr-listp addrs))
           (equal (gather-qword-addresses-corresponding-to-entries
                   addrs (wm-low-64 index val x86-equiv))
                  (gather-qword-addresses-corresponding-to-entries addrs x86)))
  :hints (("Goal"
           :in-theory (e/d* (gather-qword-addresses-corresponding-to-entries
                             ifix)
                            ()))))

(defthm gather-qword-addresses-corresponding-to-entries-wm-low-64-with-different-x86
  (implies (and (equal (gather-qword-addresses-corresponding-to-entries addrs x86-equiv)
                       (gather-qword-addresses-corresponding-to-entries addrs x86))
                (member-p index addrs)
                (mult-8-qword-paddr-listp addrs)
                (no-duplicates-p addrs)
                (xlate-equiv-entries val (rm-low-64 index x86-equiv))
                (unsigned-byte-p 64 val)
                (x86p x86-equiv))
           (equal (gather-qword-addresses-corresponding-to-entries
                   addrs (wm-low-64 index val x86-equiv))
                  (gather-qword-addresses-corresponding-to-entries addrs x86)))
  :hints (("Goal"
           :in-theory (e/d* (gather-qword-addresses-corresponding-to-entries
                             member-p)
                            (unsigned-byte-p)))))

(defthm gather-qword-addresses-corresponding-to-list-of-entries-wm-low-64-with-different-x86-disjoint
  (implies (and (equal (gather-qword-addresses-corresponding-to-list-of-entries addrs x86-equiv)
                       (gather-qword-addresses-corresponding-to-list-of-entries addrs x86))
                (pairwise-disjoint-p-aux (list index) addrs)
                (mult-8-qword-paddr-list-listp addrs)
                (physical-address-p index)
                (equal (loghead 3 index) 0))
           (equal (gather-qword-addresses-corresponding-to-list-of-entries
                   addrs (wm-low-64 index val x86-equiv))
                  (gather-qword-addresses-corresponding-to-list-of-entries addrs x86)))
  :hints (("Goal"
           :in-theory (e/d* (gather-qword-addresses-corresponding-to-list-of-entries
                             member-p)
                            (physical-address-p)))))

(defthm gather-qword-addresses-corresponding-to-list-of-entries-wm-low-64-with-different-x86
  (implies (and (equal
                 (gather-qword-addresses-corresponding-to-list-of-entries addrs x86-equiv)
                 (gather-qword-addresses-corresponding-to-list-of-entries addrs x86))
                (member-list-p index addrs)
                (mult-8-qword-paddr-list-listp addrs)
                (no-duplicates-list-p addrs)
                (xlate-equiv-entries val (rm-low-64 index x86-equiv))
                (unsigned-byte-p 64 val)
                (x86p x86-equiv))
           (equal (gather-qword-addresses-corresponding-to-list-of-entries
                   addrs (wm-low-64 index val x86-equiv))
                  (gather-qword-addresses-corresponding-to-list-of-entries addrs x86)))
  :hints (("Goal"
           :in-theory (e/d* (gather-qword-addresses-corresponding-to-list-of-entries
                             member-p)
                            (unsigned-byte-p)))))

;; (defthm gather-all-paging-structure-qword-addresses-wm-low-64-different-x86-disjoint
;;   (implies (and (equal addrs (gather-all-paging-structure-qword-addresses x86))
;;                 (equal (gather-all-paging-structure-qword-addresses x86-equiv)
;;                        addrs)
;;                 (pairwise-disjoint-p-aux (list index) addrs)
;;                 (mult-8-qword-paddr-list-listp addrs)
;;                 (physical-address-p index)
;;                 (equal (loghead 3 index) 0))
;;            (equal (gather-all-paging-structure-qword-addresses
;;                    (wm-low-64 index val x86-equiv))
;;                   (gather-all-paging-structure-qword-addresses x86)))
;;   :hints (("Goal" :in-theory (e/d* (gather-all-paging-structure-qword-addresses
;;                                     member-list-p)
;;                                    ()))))

;; (defthm gather-all-paging-structure-qword-addresses-wm-low-64-different-x86
;;   (implies (and (equal addrs (gather-all-paging-structure-qword-addresses x86))
;;                 (equal (gather-all-paging-structure-qword-addresses x86-equiv)
;;                        addrs)
;;                 (mult-8-qword-paddr-list-listp addrs)
;;                 (no-duplicates-list-p addrs)
;;                 (member-list-p index addrs)
;;                 (xlate-equiv-entries val (rm-low-64 index x86-equiv))
;;                 (unsigned-byte-p 64 val)
;;                 (x86p x86-equiv))
;;            (equal (gather-all-paging-structure-qword-addresses
;;                    (wm-low-64 index val x86-equiv))
;;                   (gather-all-paging-structure-qword-addresses x86)))
;;   :hints (("Goal" :in-theory (e/d* ()
;;                                    (gather-all-paging-structure-qword-addresses-wm-low-64-entry-addr))
;;            :use ((:instance gather-all-paging-structure-qword-addresses-wm-low-64-entry-addr
;;                             (x86 x86-equiv))
;;                  (:instance gather-all-paging-structure-qword-addresses-wm-low-64-entry-addr
;;                             (x86 x86))))))


(defthm gather-all-paging-structure-qword-addresses-wm-low-64-different-x86-disjoint
  (implies (and (xlate-equiv-x86s x86 x86-equiv)
                (good-paging-structures-x86p x86)
                (equal addrs (gather-all-paging-structure-qword-addresses x86))
                (pairwise-disjoint-p-aux (list index) addrs)
                (mult-8-qword-paddr-list-listp addrs)
                (physical-address-p index)
                (equal (loghead 3 index) 0))
           (equal (gather-all-paging-structure-qword-addresses
                   (wm-low-64 index val x86-equiv))
                  (gather-all-paging-structure-qword-addresses x86))))

(defthm gather-all-paging-structure-qword-addresses-wm-low-64-different-x86
  (implies (and (xlate-equiv-x86s x86 x86-equiv)
                (good-paging-structures-x86p x86)
                (equal addrs (gather-all-paging-structure-qword-addresses x86))
                (member-list-p index addrs)
                (xlate-equiv-entries val (rm-low-64 index x86))
                (mult-8-qword-paddr-list-listp addrs)
                (no-duplicates-list-p addrs)
                (unsigned-byte-p 64 val))
           (equal (gather-all-paging-structure-qword-addresses
                   (wm-low-64 index val x86-equiv))
                  (gather-all-paging-structure-qword-addresses x86)))
  :hints (("Goal" :in-theory (e/d* ()
                                   (gather-all-paging-structure-qword-addresses-wm-low-64-entry-addr))
           :use ((:instance gather-all-paging-structure-qword-addresses-wm-low-64-entry-addr
                            (x86 x86-equiv))
                 (:instance gather-all-paging-structure-qword-addresses-wm-low-64-entry-addr
                            (x86 x86))))))

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

(defthmd xlate-equiv-entries-at-qword-addresses-aux?-with-wm-low-64-3-helper-1
  (implies
   (and (consp addrs)
        (unsigned-byte-p 52 (+ 7 (car addrs)))
        (xlate-equiv-entries (rm-low-64 (car addrs) x86-1)
                             (rm-low-64 (car addrs) x86-2))
        (unsigned-byte-p 52 index)
        (unsigned-byte-p 52 (car addrs))
        (equal (loghead 3 (car addrs)) 0)
        (mult-8-qword-paddr-listp (cdr addrs))
        (not (member-p (car addrs) (cdr addrs)))
        (no-duplicates-p (cdr addrs))
        (member-p index (cdr addrs))
        (not (xlate-equiv-entries (rm-low-64 (car addrs) x86-1)
                                  (rm-low-64 (car addrs)
                                             (wm-low-64 index val x86-2)))))
   (not (xlate-equiv-entries-at-qword-addresses-aux? (cdr addrs)
                                                     (cdr addrs)
                                                     x86-1 x86-2)))
  :hints (("Goal" :in-theory (e/d* () (mult-8-qword-paddr-listp-and-disjoint-p))
           :use ((:instance mult-8-qword-paddr-listp-and-disjoint-p
                            (index index)
                            (addrs (cdr addrs))
                            (addr (car addrs)))))))

(defthmd xlate-equiv-entries-at-qword-addresses-aux?-with-wm-low-64-3-helper-2
  (implies (and (consp addrs)
                (unsigned-byte-p 52 (+ 7 (car addrs)))
                (not (xlate-equiv-entries (rm-low-64 (car addrs) x86-1)
                                          (rm-low-64 (car addrs) x86-2)))
                (unsigned-byte-p 52 index)
                (unsigned-byte-p 52 (car addrs))
                (equal (loghead 3 (car addrs)) 0)
                (mult-8-qword-paddr-listp (cdr addrs))
                (not (member-p (car addrs) (cdr addrs)))
                (no-duplicates-p (cdr addrs))
                (member-p index (cdr addrs))
                (xlate-equiv-entries (rm-low-64 (car addrs) x86-1)
                                     (rm-low-64 (car addrs)
                                                (wm-low-64 index val x86-2))))
           (not (xlate-equiv-entries-at-qword-addresses-aux?
                 (cdr addrs)
                 (cdr addrs)
                 x86-1 (wm-low-64 index val x86-2))))
  :hints (("Goal" :in-theory (e/d* () (mult-8-qword-paddr-listp-and-disjoint-p))
           :use ((:instance mult-8-qword-paddr-listp-and-disjoint-p
                            (index index)
                            (addrs (cdr addrs))
                            (addr (car addrs)))))))

(defthmd xlate-equiv-entries-at-qword-addresses-aux?-with-wm-low-64-3
  (implies (and (mult-8-qword-paddr-listp addrs)
                (no-duplicates-p addrs)
                (member-p index addrs)
                (xlate-equiv-entries val (rm-low-64 index x86-2))
                (unsigned-byte-p 64 val))
           (equal
            (xlate-equiv-entries-at-qword-addresses-aux?
             addrs addrs
             x86-1
             (wm-low-64 index val x86-2))
            (xlate-equiv-entries-at-qword-addresses-aux? addrs addrs x86-1 x86-2)))
  :hints (("Goal"
           :use ((:instance member-p-and-mult-8-qword-paddr-listp))
           :in-theory (e/d* (member-p
                             xlate-equiv-entries-at-qword-addresses-aux?)
                            (xlate-equiv-entries)))
          ("Subgoal *1/4"
           :use ((:instance xlate-equiv-entries-at-qword-addresses-aux?-with-wm-low-64-3-helper-1)))
          ("Subgoal *1/3"
           :use ((:instance xlate-equiv-entries-at-qword-addresses-aux?-with-wm-low-64-3-helper-2)))))

(defthm xlate-equiv-entries-at-qword-addresses?-with-wm-low-64-disjoint-new
  (implies (and (mult-8-qword-paddr-list-listp addrs)
                (not (member-list-p index addrs))
                (physical-address-p index)
                (equal (loghead 3 index) 0))
           (equal (xlate-equiv-entries-at-qword-addresses?
                   addrs
                   addrs x86-1 (wm-low-64 index val x86-2))
                  (xlate-equiv-entries-at-qword-addresses?
                   addrs addrs x86-1 x86-2)))
  :hints (("Goal" :in-theory (e/d* (xlate-equiv-entries-at-qword-addresses?
                                    member-p member-list-p)
                                   (xlate-equiv-entries)))))

(defthmd xlate-equiv-entries-at-qword-addresses?-with-wm-low-64-2-helper
  (implies (and (mult-8-qword-paddr-list-listp addrs)
                (no-duplicates-list-p addrs)
                (member-list-p index addrs)
                (physical-address-p index)  ;;
                (equal (loghead 3 index) 0) ;;
                (xlate-equiv-entries val (rm-low-64 index x86-2))
                (unsigned-byte-p 64 val)
                (xlate-equiv-entries-at-qword-addresses? addrs addrs x86-1 x86-2))
           (xlate-equiv-entries-at-qword-addresses?
            addrs addrs
            x86-1
            (wm-low-64 index val x86-2)))
  :hints (("Goal"
           ;; :use ((:instance member-list-p-and-mult-8-qword-paddr-list-listp))
           :in-theory (e/d* (member-p
                             xlate-equiv-entries-at-qword-addresses-aux?-with-wm-low-64-3
                             xlate-equiv-entries-at-qword-addresses?)
                            (xlate-equiv-entries
                             physical-address-p
                             unsigned-byte-p)))))

;; (defthm xlate-equiv-entries-at-qword-addresses?-with-wm-low-64-2
;;   (implies (and (mult-8-qword-paddr-list-listp addrs)
;;                 (no-duplicates-list-p addrs)
;;                 (member-list-p index addrs)
;;                 (xlate-equiv-entries val (rm-low-64 index x86-2))
;;                 (unsigned-byte-p 64 val)
;;                 (xlate-equiv-entries-at-qword-addresses? addrs addrs x86-1 x86-2))
;;            (xlate-equiv-entries-at-qword-addresses?
;;             addrs addrs
;;             x86-1
;;             (wm-low-64 index val x86-2)))
;;   :hints (("Goal"
;;            :use ((:instance member-list-p-and-mult-8-qword-paddr-list-listp)
;;                  (:instance xlate-equiv-entries-at-qword-addresses?-with-wm-low-64-2-helper)))))

(defthm xlate-equiv-entries-at-qword-addresses?-with-wm-low-64-2
  (implies (and (mult-8-qword-paddr-list-listp addrs)
                (no-duplicates-list-p addrs)
                (member-list-p index addrs)
                (xlate-equiv-entries val (rm-low-64 index x86-1))
                (unsigned-byte-p 64 val)
                (xlate-equiv-entries-at-qword-addresses? addrs addrs x86-1 x86-2))
           (xlate-equiv-entries-at-qword-addresses?
            addrs addrs
            x86-1
            (wm-low-64 index val x86-2)))
  :hints (("Goal"
           :in-theory (e/d* () (gather-all-paging-structure-qword-addresses-with-xlate-equiv-x86s))
           :use ((:instance member-list-p-and-mult-8-qword-paddr-list-listp)
                 (:instance xlate-equiv-entries-at-qword-addresses?-with-wm-low-64-2-helper)))))

(defthm gather-all-paging-structure-qword-addresses-mv-nth-2-ia32e-la-to-pa-PT
  ;; (i-am-here)
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
                                         (bool->bit
                                          (logbitp
                                           2
                                           (rm-low-64 (page-directory-entry-addr
                                                       lin-addr
                                                       (mv-nth 1
                                                               (page-directory-base-addr lin-addr x86)))
                                                      x86)))
                                         wp smep nxe r-w-x cpl x86)))
                            (index (page-directory-entry-addr
                                    lin-addr
                                    (mv-nth 1 (page-directory-base-addr lin-addr x86))))
                            (val (set-accessed-bit
                                  (rm-low-64 (page-directory-entry-addr
                                              lin-addr
                                              (mv-nth 1
                                                      (page-directory-base-addr lin-addr x86)))
                                             x86)))
                            (addrs (gather-all-paging-structure-qword-addresses x86))
                            (x86 x86)))
           :in-theory (e/d* (ia32e-la-to-pa-page-directory
                             entry-found-p-and-lin-addr
                             good-paging-structures-x86p)
                            (bitops::logand-with-negated-bitmask
                             entry-found-p-and-good-paging-structures-x86p
                             xlate-equiv-x86s-and-page-table-entry-addr-address
                             xlate-equiv-x86s-and-page-table-base-addr-address
                             no-duplicates-list-p
                             gather-all-paging-structure-qword-addresses-wm-low-64-different-x86)))))


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
                             gather-all-paging-structure-qword-addresses-with-xlate-equiv-x86s)))))

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
