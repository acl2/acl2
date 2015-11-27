;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")
(include-book "gather-paging-structures-thms" :ttags :all)

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))
(local (include-book "centaur/gl/gl" :dir :system))

(local (in-theory (e/d (entry-found-p-and-lin-addr
                        entry-found-p-and-good-paging-structures-x86p)
                       ())))

;; ======================================================================

(local
 (def-gl-thm logand-loghead-and-page-table-base-addr-helper
   :hyp (unsigned-byte-p 64 x)
   :concl (equal (logand 18446744073709547520 (ash (loghead 40 (logtail 12 x)) 12))
                 (ash (loghead 40 (logtail 12 x)) 12))
   :g-bindings `((x (:g-number ,(gl-int 0 1 65))))))

(defthm mv-nth-2-page-table-entry-no-page-fault-p-value-no-error
  (implies (not (mv-nth 0 (page-table-entry-no-page-fault-p
                           lin-addr entry u-s-acc wp smep nxe r-w-x cpl x86)))
           (equal
            (mv-nth 2 (page-table-entry-no-page-fault-p
                       lin-addr entry u-s-acc wp smep nxe r-w-x cpl x86))
            x86))
  :hints (("Goal" :in-theory (e/d* (page-table-entry-no-page-fault-p) ()))))

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

(defthmd ia32e-la-to-pa-PT-with-xlate-equiv-x86s
  ;; TO-DO: Speed this up.
  (implies (xlate-equiv-x86s x86-1 x86-2)
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
                             ia32e-la-to-pa-page-table
                             ;; I should prove useful lemmas about the
                             ;; following two functions to speed this
                             ;; theorem up.
                             PAGE-TABLE-ENTRY-NO-PAGE-FAULT-P
                             PAGE-FAULT-EXCEPTION)
                            (xlate-equiv-x86s
                             xlate-equiv-x86s-and-page-table-entry-addr-value
                             xlate-equiv-x86s-and-page-table-base-addr-address
                             xlate-equiv-x86s-and-page-table-entry-addr-address
                             page-table-entry-addr-found-p-and-xlate-equiv-x86s
                             bitops::logand-with-negated-bitmask
                             bitops::logior-equal-0))
           :use ((:instance xlate-equiv-x86s-and-page-table-entry-addr-value)
                 (:instance xlate-equiv-entries-open
                            (e1 (rm-low-64
                                 (page-table-entry-addr
                                  lin-addr
                                  (mv-nth 1 (page-table-base-addr lin-addr x86-2)))
                                 x86-1))
                            (e2 (rm-low-64
                                 (page-table-entry-addr
                                  lin-addr
                                  (mv-nth 1 (page-table-base-addr lin-addr x86-2)))
                                 x86-2)))
                 (:instance page-table-entry-addr-found-p-and-xlate-equiv-x86s
                            (x86-1 x86-1)
                            (x86-2 x86-2))
                 (:instance page-table-entry-addr-found-p-and-xlate-equiv-x86s
                            (x86-1 x86-2)
                            (x86-2 x86-1))
                 (:instance xlate-equiv-x86s-and-page-table-base-addr-address)
                 ;; xlate-equiv-entries-and-loghead
                 (:instance xlate-equiv-entries-and-loghead
                            (e1 (rm-low-64
                                 (page-table-entry-addr
                                  lin-addr
                                  (mv-nth 1 (page-table-base-addr lin-addr x86-2)))
                                 x86-1))
                            (e2 (rm-low-64
                                 (page-table-entry-addr
                                  lin-addr
                                  (mv-nth 1 (page-table-base-addr lin-addr x86-2)))
                                 x86-2))
                            (n 1))
                 ;; xlate-equiv-entries-and-logtail
                 (:instance xlate-equiv-entries-and-logtail
                            (e1 (rm-low-64
                                 (page-table-entry-addr
                                  lin-addr
                                  (mv-nth 1 (page-table-base-addr lin-addr x86-2)))
                                 x86-1))
                            (e2 (rm-low-64
                                 (page-table-entry-addr
                                  lin-addr
                                  (mv-nth 1 (page-table-base-addr lin-addr x86-2)))
                                 x86-2))
                            (n 12))
                 (:instance xlate-equiv-entries-and-logtail
                            (e1 (rm-low-64
                                 (page-table-entry-addr
                                  lin-addr
                                  (mv-nth 1 (page-table-base-addr lin-addr x86-2)))
                                 x86-1))
                            (e2 (rm-low-64
                                 (page-table-entry-addr
                                  lin-addr
                                  (mv-nth 1 (page-table-base-addr lin-addr x86-2)))
                                 x86-2))
                            (n 52))
                 ;; loghead-smaller-and-logbitp
                 (:instance loghead-smaller-and-logbitp
                            (e1 (rm-low-64
                                 (page-table-entry-addr
                                  lin-addr
                                  (mv-nth 1 (page-table-base-addr lin-addr x86-2)))
                                 x86-1))
                            (e2 (rm-low-64
                                 (page-table-entry-addr
                                  lin-addr
                                  (mv-nth 1 (page-table-base-addr lin-addr x86-2)))
                                 x86-2))
                            (m 1)
                            (n 5))
                 (:instance loghead-smaller-and-logbitp
                            (e1 (rm-low-64
                                 (page-table-entry-addr
                                  lin-addr
                                  (mv-nth 1 (page-table-base-addr lin-addr x86-2)))
                                 x86-1))
                            (e2 (rm-low-64
                                 (page-table-entry-addr
                                  lin-addr
                                  (mv-nth 1 (page-table-base-addr lin-addr x86-2)))
                                 x86-2))
                            (m 2)
                            (n 5))
                 ;; logtail-bigger-and-logbitp
                 (:instance logtail-bigger-and-logbitp
                            (e1 (rm-low-64
                                 (page-table-entry-addr
                                  lin-addr
                                  (mv-nth 1 (page-table-base-addr lin-addr x86-2)))
                                 x86-1))
                            (e2 (rm-low-64
                                 (page-table-entry-addr
                                  lin-addr
                                  (mv-nth 1 (page-table-base-addr lin-addr x86-2)))
                                 x86-2))
                            (m 7)
                            (n 52))
                 (:instance logtail-bigger-and-logbitp
                            (e1 (rm-low-64
                                 (page-table-entry-addr
                                  lin-addr
                                  (mv-nth 1 (page-table-base-addr lin-addr x86-2)))
                                 x86-1))
                            (e2 (rm-low-64
                                 (page-table-entry-addr
                                  lin-addr
                                  (mv-nth 1 (page-table-base-addr lin-addr x86-2)))
                                 x86-2))
                            (m 7)
                            (n 63))))))

(defthm mv-nth-0-ia32e-la-to-pa-PT-with-xlate-equiv-x86s
  (implies (xlate-equiv-x86s x86-1 x86-2)
           (equal (mv-nth
                   0
                   (ia32e-la-to-pa-PT
                    lin-addr u-s-acc wp smep nxe r-w-x cpl x86-1))
                  (mv-nth
                   0
                   (ia32e-la-to-pa-PT
                    lin-addr u-s-acc wp smep nxe r-w-x cpl x86-2))))
  :hints (("Goal" :use ((:instance ia32e-la-to-pa-PT-with-xlate-equiv-x86s))))
  :rule-classes :congruence)

(defthm mv-nth-1-ia32e-la-to-pa-PT-with-xlate-equiv-x86s
  (implies (xlate-equiv-x86s x86-1 x86-2)
           (equal (mv-nth
                   1
                   (ia32e-la-to-pa-PT
                    lin-addr u-s-acc wp smep nxe r-w-x cpl x86-1))
                  (mv-nth
                   1
                   (ia32e-la-to-pa-PT
                    lin-addr u-s-acc wp smep nxe r-w-x cpl x86-2))))
  :hints (("Goal" :use ((:instance ia32e-la-to-pa-PT-with-xlate-equiv-x86s))))
  :rule-classes :congruence)

(defthm xlate-equiv-x86s-with-mv-nth-2-ia32e-la-to-pa-PT
  (xlate-equiv-x86s
   (mv-nth 2 (ia32e-la-to-pa-PT lin-addr u-s-acc wp smep nxe r-w-x cpl x86))
   x86)
  :hints (("Goal" :do-not '(preprocess)
           :use ((:instance entry-found-p-and-good-paging-structures-x86p))
           :in-theory (e/d* (ia32e-la-to-pa-page-table
                             good-paging-structures-x86p)
                            (bitops::logand-with-negated-bitmask
                             xlate-equiv-x86s-and-page-table-entry-addr-address
                             xlate-equiv-x86s-and-page-table-base-addr-address
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
  (implies ;; (page-directory-entry-addr-found-p lin-addr x86)
   ;; (page-table-entry-addr-found-p lin-addr x86)
   (good-paging-structures-x86p x86)
   (equal (gather-all-paging-structure-qword-addresses
           (mv-nth 2 (ia32e-la-to-pa-PT lin-addr u-s-acc wp smep nxe r-w-x cpl x86)))
          (gather-all-paging-structure-qword-addresses x86)))
  :hints (("Goal"
           :use ((:instance
                  gather-all-paging-structure-qword-addresses-with-xlate-equiv-x86s
                  (x86-equiv (mv-nth 2 (ia32e-la-to-pa-PT lin-addr u-s-acc wp smep nxe r-w-x cpl x86))))))))

(defthm xlate-equiv-entries-at-qword-addresses?-mv-nth-2-ia32e-la-to-pa-PT
  (implies (and (good-paging-structures-x86p x86)
                (equal addrs (gather-all-paging-structure-qword-addresses x86)))
           (equal (xlate-equiv-entries-at-qword-addresses?
                   addrs addrs
                   x86
                   (mv-nth 2 (ia32e-la-to-pa-PT lin-addr u-s-acc wp smep nxe r-w-x cpl x86)))
                  (xlate-equiv-entries-at-qword-addresses? addrs addrs x86 x86)))
  :hints (("Goal"
           :use ((:instance xlate-equiv-x86s-and-xlate-equiv-entries-at-qword-addresses?
                            (addrs addrs)
                            (x86 x86)
                            (x86-equiv
                             (mv-nth 2 (ia32e-la-to-pa-PT lin-addr u-s-acc wp smep nxe r-w-x cpl x86))))))))

;; ======================================================================

;; (defthm page-table-entry-addr-found-p-after-a-page-walk
;;   (implies (and (page-table-entry-addr-found-p lin-addr-1 x86)
;;                 (page-table-entry-addr-found-p lin-addr-2 x86)
;;                 (good-paging-structures-x86p x86))
;;            (page-table-entry-addr-found-p
;;             lin-addr-1
;;             (mv-nth 2
;;                     (ia32e-la-to-pa-page-table
;;                      lin-addr-2
;;                      (mv-nth 1 (page-table-base-addr lin-addr-2 x86))
;;                      u-s-acc-2
;;                      wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
;;   :hints (("Goal"
;;            :use ((:instance logand-loghead-and-page-table-base-addr
;;                             (lin-addr lin-addr-2))
;;                  (:instance page-table-entry-addr-found-p-and-xlate-equiv-x86s
;;                             (x86-1 x86)
;;                             (lin-addr lin-addr-1)
;;                             (x86-2
;;                              (mv-nth 2
;;                                      (ia32e-la-to-pa-page-table
;;                                       lin-addr-2
;;                                       (mv-nth 1 (page-table-base-addr lin-addr-2 x86))
;;                                       u-s-acc-2
;;                                       wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
;;                  (:instance xlate-equiv-x86s-with-mv-nth-2-ia32e-la-to-pa-PT
;;                             (x86 x86)
;;                             (lin-addr lin-addr-2)
;;                             (u-s-acc u-s-acc-2)
;;                             (wp wp-2)
;;                             (smep smep-2)
;;                             (nxe nxe-2)
;;                             (r-w-x r-w-x-2)
;;                             (cpl cpl-2)))
;;            :in-theory (e/d* ()
;;                             (physical-address-p
;;                              page-table-entry-addr-found-p-and-xlate-equiv-x86s
;;                              xlate-equiv-x86s-with-mv-nth-2-ia32e-la-to-pa-PT
;;                              xlate-equiv-x86s-and-page-dir-ptr-table-base-addr-address
;;                              xlate-equiv-x86s-and-page-dir-ptr-table-entry-addr-address
;;                              xlate-equiv-x86s-and-page-directory-base-addr-address
;;                              xlate-equiv-x86s-and-page-directory-base-addr-error
;;                              xlate-equiv-x86s-and-page-directory-entry-addr-address
;;                              xlate-equiv-x86s-and-page-table-base-addr-address
;;                              xlate-equiv-x86s-and-page-table-entry-addr-address
;;                              bitops::logand-with-negated-bitmask)))))
